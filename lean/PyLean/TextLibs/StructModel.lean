import PyLean.TextLibs.Bits

/-!
Model of `Modules/_struct.c` (CPython 3.14.7) on an LP64 little-endian build
(`SIZEOF_LONG = 8`, `PY_LITTLE_ENDIAN = 1`), which is the x86-64 build the
difftest runs on.

The three format tables and `init_endian_tables` are mirrored literally: table
entries name their pack and unpack routines through the `UFn`/`PFn` enumerations
and the swap of native routines into `lilendian_table` is computed, not assumed.
`Struct` objects are the pair `(codes, s_size, s_len)` from `prepare_s`.

Arguments can fail. `SV.obj` is an object by what it does: `__index__`, `__float__`, `__complex__`
and `__bool__` can each raise, and `BufArg` and `OffArg` do the same for buffers and offsets. A
conversion can also call `__init__` on the `Struct` in use, which frees `s_codes` and changes
`s_size` and `s_len` under the running C function. When the C then reads freed memory or past an
array, the result is `MEMORY`: that is undefined behaviour rather than an outcome, so it is stated
and refuted but never compared with CPython.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

/-- An object handed to `pack`, by what its conversions do. `none` is a missing method. `reinit` says
that the conversion this format uses also calls `__init__` with a valid format on the `Struct` that
is packing. -/
structure PyO where
  index : Option (Py Int) := none
  float : Option (Py Nat) := none
  cplx : Option (Py (Nat × Nat)) := none
  truth : Py Bool := .ok true
  reinit : Bool := false
  deriving DecidableEq, Inhabited

instance : Repr PyO := ⟨fun _ _ => "PyO"⟩

/-- Python objects handed to `pack`, and objects `unpack` returns. -/
inductive SV where
  /-- `int` (and `bool`, which is an `int` subclass for every integer code). -/
  | int (n : Int)
  /-- A non-int object with `__index__` returning `n`. -/
  | index (n : Int)
  | bytes (b : List Nat)
  | bytearray (b : List Nat)
  /-- A `float`, by its 64-bit pattern. -/
  | float (bits : Nat)
  | cplx (re im : Nat)
  /-- The result type of `?`. -/
  | bool (b : Bool)
  /-- Any other object, with its truth value (`str`, `None`, ...). -/
  | other (truth : Bool)
  /-- An object with conversions that can raise and re-enter. -/
  | obj (o : PyO)
  deriving Repr, DecidableEq, Inhabited

/-- `struct.error`. -/
def structErr (m : String) : PyExc := .named "error" m

/-- Undefined behaviour in C: a read of freed memory or past an array, or a division by zero. Not a
Python exception. -/
def MEMORY : PyExc := .named "MemoryUnsafe" ""

/-- The unpack routines of the three tables (`Modules/_struct.c:366-522, 865-993, 1196-1317`). -/
inductive UFn where
  | none | nuByte | nuUbyte | nuChar | nuShort | nuUshort | nuInt | nuUint | nuLong | nuUlong
  | nuSsizeT | nuSizeT | nuLonglong | nuUlonglong | nuBool | nuHalffloat | nuFloat | nuDouble
  | nuFloatComplex | nuDoubleComplex | nuVoidP
  | buShort | buUint | buInt | buLonglong | buUlonglong | buBool | buHalffloat | buFloat
  | buDouble | buFloatComplex | buDoubleComplex
  | luShort | luUint | luInt | luLonglong | luUlonglong | luHalffloat | luFloat | luDouble
  | luFloatComplex | luDoubleComplex
  deriving Repr, DecidableEq, Inhabited

/-- The pack routines of the three tables (`Modules/_struct.c:524-835, 995-1167, 1320-1481`). -/
inductive PFn where
  | none | npByte | npUbyte | npChar | npShort | npUshort | npInt | npUint | npLong | npUlong
  | npSsizeT | npSizeT | npLonglong | npUlonglong | npBool | npHalffloat | npFloat | npDouble
  | npFloatComplex | npDoubleComplex | npVoidP
  | bpInt | bpUint | bpLonglong | bpUlonglong | bpBool | bpHalffloat | bpFloat | bpDouble
  | bpFloatComplex | bpDoubleComplex
  | lpInt | lpUint | lpLonglong | lpUlonglong | lpHalffloat | lpFloat | lpDouble
  | lpFloatComplex | lpDoubleComplex
  deriving Repr, DecidableEq, Inhabited

/-- `formatdef`, `Modules/_struct.c:47-55`. -/
structure FormatDef where
  format : Char
  size : Nat
  alignment : Nat
  unpack : UFn
  pack : PFn
  deriving Repr, DecidableEq, Inhabited

/-- `native_table`, `Modules/_struct.c:837-864`, with x86-64 sizes. -/
def nativeTable : List FormatDef :=
  [⟨'x', 1, 0, .none, .none⟩, ⟨'b', 1, 0, .nuByte, .npByte⟩, ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'c', 1, 0, .nuChar, .npChar⟩, ⟨'s', 1, 0, .none, .none⟩, ⟨'p', 1, 0, .none, .none⟩,
   ⟨'h', 2, 2, .nuShort, .npShort⟩, ⟨'H', 2, 2, .nuUshort, .npUshort⟩,
   ⟨'i', 4, 4, .nuInt, .npInt⟩, ⟨'I', 4, 4, .nuUint, .npUint⟩,
   ⟨'l', 8, 8, .nuLong, .npLong⟩, ⟨'L', 8, 8, .nuUlong, .npUlong⟩,
   ⟨'n', 8, 8, .nuSsizeT, .npSsizeT⟩, ⟨'N', 8, 8, .nuSizeT, .npSizeT⟩,
   ⟨'q', 8, 8, .nuLonglong, .npLonglong⟩, ⟨'Q', 8, 8, .nuUlonglong, .npUlonglong⟩,
   ⟨'?', 1, 1, .nuBool, .npBool⟩, ⟨'e', 2, 2, .nuHalffloat, .npHalffloat⟩,
   ⟨'f', 4, 4, .nuFloat, .npFloat⟩, ⟨'d', 8, 8, .nuDouble, .npDouble⟩,
   ⟨'F', 8, 4, .nuFloatComplex, .npFloatComplex⟩, ⟨'D', 16, 8, .nuDoubleComplex, .npDoubleComplex⟩,
   ⟨'P', 8, 8, .nuVoidP, .npVoidP⟩]

/-- `bigendian_table`, `Modules/_struct.c:1172-1195`. -/
def bigendianTable : List FormatDef :=
  [⟨'x', 1, 0, .none, .none⟩, ⟨'b', 1, 0, .nuByte, .npByte⟩, ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'c', 1, 0, .nuChar, .npChar⟩, ⟨'s', 1, 0, .none, .none⟩, ⟨'p', 1, 0, .none, .none⟩,
   ⟨'h', 2, 0, .buShort, .bpInt⟩, ⟨'H', 2, 0, .buUint, .bpUint⟩,
   ⟨'i', 4, 0, .buInt, .bpInt⟩, ⟨'I', 4, 0, .buUint, .bpUint⟩,
   ⟨'l', 4, 0, .buInt, .bpInt⟩, ⟨'L', 4, 0, .buUint, .bpUint⟩,
   ⟨'q', 8, 0, .buLonglong, .bpLonglong⟩, ⟨'Q', 8, 0, .buUlonglong, .bpUlonglong⟩,
   ⟨'?', 1, 0, .buBool, .bpBool⟩, ⟨'e', 2, 0, .buHalffloat, .bpHalffloat⟩,
   ⟨'f', 4, 0, .buFloat, .bpFloat⟩, ⟨'d', 8, 0, .buDouble, .bpDouble⟩,
   ⟨'F', 8, 0, .buFloatComplex, .bpFloatComplex⟩, ⟨'D', 16, 0, .buDoubleComplex, .bpDoubleComplex⟩]

/-- `lilendian_table` before `init_endian_tables` runs, `Modules/_struct.c:1488-1513`. -/
def lilendianTable0 : List FormatDef :=
  [⟨'x', 1, 0, .none, .none⟩, ⟨'b', 1, 0, .nuByte, .npByte⟩, ⟨'B', 1, 0, .nuUbyte, .npUbyte⟩,
   ⟨'c', 1, 0, .nuChar, .npChar⟩, ⟨'s', 1, 0, .none, .none⟩, ⟨'p', 1, 0, .none, .none⟩,
   ⟨'h', 2, 0, .luShort, .lpInt⟩, ⟨'H', 2, 0, .luUint, .lpUint⟩,
   ⟨'i', 4, 0, .luInt, .lpInt⟩, ⟨'I', 4, 0, .luUint, .lpUint⟩,
   ⟨'l', 4, 0, .luInt, .lpInt⟩, ⟨'L', 4, 0, .luUint, .lpUint⟩,
   ⟨'q', 8, 0, .luLonglong, .lpLonglong⟩, ⟨'Q', 8, 0, .luUlonglong, .lpUlonglong⟩,
   ⟨'?', 1, 0, .buBool, .bpBool⟩, ⟨'e', 2, 0, .luHalffloat, .lpHalffloat⟩,
   ⟨'f', 4, 0, .luFloat, .lpFloat⟩, ⟨'d', 8, 0, .luDouble, .lpDouble⟩,
   ⟨'F', 8, 0, .luFloatComplex, .lpFloatComplex⟩, ⟨'D', 16, 0, .luDoubleComplex, .lpDoubleComplex⟩]

/-- The inner `while (ptr->format != '\0')` of `init_endian_tables`: returns the
updated table and the advanced `other` index. -/
def initInner (native : FormatDef) (tbl : List FormatDef) (other : Nat) :
    (ptr : Nat) → (fuel : Nat) → List FormatDef × Nat
  | _, 0 => (tbl, other)
  | ptr, fuel + 1 =>
    match tbl[ptr]? with
    | none => (tbl, other)
    | some p =>
      if p.format = native.format then
        let other' := if ptr = other then other + 1 else other
        if p.size ≠ native.size then (tbl, other')
        else if p.format = 'd' ∨ p.format = 'f' then (tbl, other')
        else if p.format = '?' then (tbl, other')
        else (tbl.set ptr { p with pack := native.pack, unpack := native.unpack }, other')
      else initInner native tbl other (ptr + 1) fuel

/-- `init_endian_tables`, `Modules/_struct.c:1518-1557`. -/
def initEndianTablesGo (tbl : List FormatDef) (other : Nat) : List FormatDef → List FormatDef
  | [] => tbl
  | n :: ns =>
    if other ≥ tbl.length then tbl
    else
      let (tbl', other') := initInner n tbl other other tbl.length
      initEndianTablesGo tbl' other' ns

def lilendianTable : List FormatDef := initEndianTablesGo lilendianTable0 0 nativeTable

/-- Which table a format uses. -/
inductive Tab where | native | little | big
  deriving Repr, DecidableEq, Inhabited

def Tab.table : Tab → List FormatDef
  | .native => nativeTable
  | .little => lilendianTable
  | .big => bigendianTable

/-- `whichtable`, `Modules/_struct.c:1560-1583`: table and the remaining format. -/
def whichtable : List Char → Tab × List Char
  | '<' :: r => (.little, r)
  | '>' :: r | '!' :: r => (.big, r)
  | '=' :: r => (.little, r)
  | '@' :: r => (.native, r)
  | s => (.native, s)

/-- `getentry`, `Modules/_struct.c:1603-1613`. -/
def getentry (c : Char) : List FormatDef → Py FormatDef
  | [] => .error (structErr "bad char in struct format")
  | f :: fs => if f.format = c then .ok f else getentry c fs

/-- `PY_SSIZE_T_MAX` as a `Nat`. -/
def maxN : Nat := 2 ^ 63 - 1

/-- `align`, `Modules/_struct.c:1618-1632`: `none` is the `-1` overflow return.
`e->format == c` always holds at both call sites. -/
def align (size : Nat) (e : FormatDef) : Option Nat :=
  if e.alignment ≠ 0 ∧ size > 0 then
    let extra := (e.alignment - 1) - (size - 1) % e.alignment
    if extra > maxN - size then none else some (size + extra)
  else some size

/-- `Py_ISSPACE`. -/
def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\t' || c = '\n' || c = '\r' || c = '\x0b' || c = '\x0c'

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def digit (c : Char) : Nat := c.toNat - '0'.toNat

/-- The digit loop of the first pass, `Modules/_struct.c:1677-1685`. The `none` result
is `goto overflow`; otherwise `(num, c, rest)`, where `c` is the first non-digit read
(`none` for the terminating NUL). -/
def scanDigits1 (num : Nat) : List Char → Option (Nat × Option Char × List Char)
  | [] => some (num, none, [])
  | c :: r =>
    if isDigit c then
      if num ≥ maxN / 10 ∧ (num > maxN / 10 ∨ digit c > maxN % 10) then none
      else scanDigits1 (num * 10 + digit c) r
    else some (num, some c, r)

def overflowErr : PyExc := structErr "total struct size too long"

/-- State of the first pass of `prepare_s`. -/
structure Pass1 where
  size : Nat := 0
  len : Nat := 0
  ncodes : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- One format item of the first pass, `Modules/_struct.c@3.14.7:1672-1705`. -/
def pass1Item (tbl : List FormatDef) (st : Pass1) (num : Nat) (c : Char) : Py Pass1 := do
  let e ← getentry c tbl
  let (len, ncodes) ←
    if c = 's' ∨ c = 'p' then
      if st.len = maxN then Except.error overflowErr
      else pure (st.len + 1, st.ncodes + 1)
    else if c = 'x' then pure (st.len, st.ncodes)
    else
      if num > maxN - st.len then Except.error overflowErr
      else pure (st.len + num, if num ≠ 0 then st.ncodes + 1 else st.ncodes)
  let itemsize := e.size
  match align st.size e with
  | none => .error overflowErr
  | some size =>
    if num > (maxN - size) / itemsize then .error overflowErr
    else pure { size := size + num * itemsize, len, ncodes }

/-- The first `while` of `prepare_s`, `Modules/_struct.c:1672-1731`. -/
def pass1 (tbl : List FormatDef) : (fuel : Nat) → List Char → Pass1 → Py Pass1
  | 0, _, _ => .error .modelFuel
  | _ + 1, [], st => pure st
  | fuel + 1, c :: s, st =>
    if isSpace c then pass1 tbl fuel s st
    else if isDigit c then
      match scanDigits1 (digit c) s with
      | none => .error overflowErr
      | some (_, none, _) => .error (structErr "repeat count given without format specifier")
      | some (num, some c', r) => do pass1 tbl fuel r (← pass1Item tbl st num c')
    else do pass1 tbl fuel s (← pass1Item tbl st 1 c)

/-- `formatcode`, `Modules/_struct.c:57-62`. -/
structure Code where
  fmtdef : FormatDef
  offset : Nat
  size : Nat
  repeat_ : Nat
  deriving Repr, DecidableEq, Inhabited

/-- The digit loop of the second pass, `Modules/_struct.c:1752-1753`. -/
def scanDigits2 (num : Nat) : List Char → Nat × Option Char × List Char
  | [] => (num, none, [])
  | c :: r => if isDigit c then scanDigits2 (num * 10 + digit c) r else (num, some c, r)

/-- One item of the second pass, `Modules/_struct.c@3.14.7:1733-1752`. `getentry` and `align`
cannot fail here because the first pass accepted the format. -/
def pass2Item (tbl : List FormatDef) (acc : List Code × Nat) (num : Nat) (c : Char) :
    List Code × Nat :=
  let (codes, size) := acc
  match getentry c tbl with
  | .error _ => acc
  | .ok e =>
    let size := (align size e).getD size
    if c = 's' ∨ c = 'p' then (codes ++ [⟨e, size, num, 1⟩], size + num)
    else if c = 'x' then (codes, size + num)
    else if num ≠ 0 then (codes ++ [⟨e, size, e.size, num⟩], size + e.size * num)
    else (codes, size)

/-- The second `while` of `prepare_s`, `Modules/_struct.c:1747-1780`. -/
def pass2 (tbl : List FormatDef) : (fuel : Nat) → List Char → List Code × Nat → List Code × Nat
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | fuel + 1, c :: s, acc =>
    if isSpace c then pass2 tbl fuel s acc
    else if isDigit c then
      match scanDigits2 (digit c) s with
      | (_, none, _) => acc
      | (num, some c', r) => pass2 tbl fuel r (pass2Item tbl acc num c')
    else pass2 tbl fuel s (pass2Item tbl acc 1 c)

/-- An initialised `Struct` object. -/
structure SObj where
  codes : List Code
  sSize : Nat
  sLen : Nat
  format : List Nat
  deriving Repr, DecidableEq, Inhabited

def asciiChars (b : List Nat) : List Char := b.map Char.ofNat

/-- `prepare_s`, `Modules/_struct.c:1640-1800`. `sizeof(formatcode) = 32`. -/
def prepareS (format : List Nat) : Py SObj :=
  if 0 ∈ format then .error (structErr "embedded null character")
  else
    let (t, fmt) := whichtable (asciiChars format)
    match pass1 t.table (fmt.length + 1) fmt {} with
    | .error e => .error e
    | .ok st =>
      if st.ncodes + 1 > maxN / 32 then .error (.named "MemoryError" "")
      else
        let (codes, size) := pass2 t.table (fmt.length + 1) fmt ([], 0)
        .ok ⟨codes, size, st.len, format⟩

/-- The argument of `Struct()` and of the module functions. -/
inductive FmtArg where
  | str (cps : List Nat)
  | bytes (b : List Nat)
  /-- Any other object: its type name, and whether it is hashable. -/
  | other (tyName : String) (hashable : Bool)
  /-- An object whose `__hash__` raises. -/
  | hashRaises (tyName : String) (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- `Struct___init___impl`, `Modules/_struct.c:1964-2004`. -/
def structInit : FmtArg → Py SObj
  | .str cps =>
    if cps.all (· < 128) then prepareS cps
    else .error (.named "UnicodeEncodeError" "~'ascii' codec can't encode character")
  | .bytes b => prepareS b
  | .other t _ | .hashRaises t _ =>
    .error (.typeError s!"Struct() argument 1 must be a str or bytes object, not {t}")

/-- `cache_struct_converter`, `Modules/_struct.c:2615-2663`. A cache hit returns the
object built by an earlier identical call, so the cache is not observable; only the
key conversion (surrogateescape decoding of bytes, then `Struct(key)`) and the hash
of the key are. -/
def cacheStruct : FmtArg → Py SObj
  | .bytes b => structInit (.str (b.map (fun x => if x < 128 then x else 0xDC00 + x)))
  | .str s => structInit (.str s)
  | .other t hashable =>
    if hashable then structInit (.other t hashable)
    else .error (.typeError s!"cannot use '{t}' as a dict key (unhashable type: '{t}')")
  | .hashRaises t e =>
    match e with
    | .typeError m => .error (.typeError s!"cannot use '{t}' as a dict key ({m})")
    | e => .error e

/-- `_range_error`, `Modules/_struct.c:315-343`. -/
def rangeError (f : FormatDef) (isUnsigned : Bool) : PyExc :=
  let ulargest := 2 ^ (f.size * 8) - 1
  if isUnsigned then
    structErr s!"'{f.format}' format requires 0 <= number <= {ulargest}"
  else
    let largest := ulargest / 2
    structErr s!"'{f.format}' format requires {-(largest : Int) - 1} <= number <= {largest}"

/-- `get_pylong`, `Modules/_struct.c:112-134`. -/
def getPylong : SV → Py Int
  | .int n | .index n => .ok n
  | .obj { index := some r, .. } => r
  | _ => .error (structErr "required argument is not an integer")

/-- A C integer conversion, raising `OverflowError msg` outside `[lo, hi]`. -/
def asC (lo hi : Int) (msg : String) (n : Int) : Py Int :=
  if n < lo ∨ n > hi then .error (.overflowError msg) else .ok n

def longMin : Int := -(2 ^ 63)
def longMax : Int := 2 ^ 63 - 1
def ulongMax : Int := 2 ^ 64 - 1

/-- `get_long`, `Modules/_struct.c:139-155` (with `PyLong_AsLong`). -/
def getLong (v : SV) : Py Int := do
  asC longMin longMax "Python int too large to convert to C long" (← getPylong v)

/-- `get_ulong`, `Modules/_struct.c:160-176` (with `PyLong_AsUnsignedLong`). -/
def getUlong (v : SV) : Py Int := do
  let n ← getPylong v
  if n < 0 then throw (.overflowError "can't convert negative int to unsigned")
  asC 0 ulongMax "Python int too large to convert to C unsigned long" n

/-- `get_longlong`, `Modules/_struct.c:180-196`. -/
def getLonglong (v : SV) : Py Int := do
  asC longMin longMax "Python int too large to convert to C long long" (← getPylong v)

/-- `get_ulonglong`, `Modules/_struct.c:200-216`. -/
def getUlonglong (v : SV) : Py Int := do
  let n ← getPylong v
  if n < 0 then throw (.overflowError "can't convert negative int to unsigned")
  asC 0 ulongMax "Python int too large to convert" n

/-- `get_ssize_t`, `Modules/_struct.c:220-236`. -/
def getSsizeT (v : SV) : Py Int := do
  asC longMin longMax "Python int too large to convert to C ssize_t" (← getPylong v)

/-- `get_size_t`, `Modules/_struct.c:240-256`. -/
def getSizeT (v : SV) : Py Int := do
  let n ← getPylong v
  if n < 0 then throw (.overflowError "can't convert negative int to size_t")
  asC 0 ulongMax "Python int too large to convert to C size_t" n

/-- `if (get_*(...) < 0) { if (PyErr_ExceptionMatches(PyExc_OverflowError))
RANGE_ERROR(...); return -1; }`. -/
def orRange (f : FormatDef) (isUnsigned : Bool) (r : Py Int) : Py Int :=
  match r with
  | .error (.overflowError _) => .error (rangeError f isUnsigned)
  | r => r

/-- Two's-complement bytes of `x`, little-endian (`memcpy(p, &y, sizeof y)`). -/
def twos (size : Nat) (x : Int) : List Nat :=
  leBytes size ((x % (2 ^ (size * 8) : Int)).toNat)

/-- `Struct`'s native 2-, 4-, 8-byte integer pack routines (`np_short`, `np_int`, `np_long`,
`np_ssize_t`) on the value `get_long`/`get_ssize_t` returned. -/
def npSigned (f : FormatDef) (lo hi : Int) (x : Int) : Py (List Nat) :=
  if x < lo ∨ x > hi then .error (rangeError f false) else .ok (twos f.size x)

/-- `np_uint`, `np_ushort`: range check on the unsigned value. -/
def npUnsigned (f : FormatDef) (hi : Int) (x : Int) : Py (List Nat) :=
  if x < 0 ∨ x > hi then .error (rangeError f true) else .ok (twos f.size x)

/-- The `do { q[--i] = x & 0xff; x >>= 8; } while (i > 0)` of `bp_int`/`bp_uint`. -/
def bpLoop : Nat → Int → List Nat
  | 0, _ => []
  | i + 1, x => bpLoop i (x / 256) ++ [(x % 256).toNat]

/-- The `do { *q++ = x & 0xff; x >>= 8; } while (--i > 0)` of `lp_int`/`lp_uint`. -/
def lpLoop : Nat → Int → List Nat
  | 0, _ => []
  | i + 1, x => (x % 256).toNat :: lpLoop i (x / 256)

/-- `PyObject_IsTrue`. -/
def isTrue : SV → Py Bool
  | .int n => .ok (n != 0)
  -- an object with `__index__` but no `__bool__`/`__len__` is always true
  | .index _ => .ok true
  | .bytes b | .bytearray b => .ok !b.isEmpty
  | .float x => .ok (f64.frac x != 0 || f64.expOf x != 0)
  | .cplx a b => .ok ((f64.frac a != 0 || f64.expOf a != 0) || (f64.frac b != 0 || f64.expOf b != 0))
  | .bool b => .ok b
  | .other t => .ok t
  | .obj o => o.truth

/-- `Py` to `Option`: `struct` replaces every exception from these two conversions, a raising
`__float__` included, `Modules/_struct.c:281-286`. -/
def okOf {α : Type} : Py α → Option α
  | .ok a => some a
  | .error _ => none

/-- `PyFloat_AsDouble`: `none` for every failure. `__float__` comes before `__index__`. -/
def asDouble : SV → Option Nat
  | .float x => some x
  | .int n | .index n => intToDouble n
  | .bool b => some (if b then 0x3FF0000000000000 else 0)
  | .obj o =>
    match o.float with
    | some r => okOf r
    | none =>
      match o.index with
      | some r => (okOf r).bind intToDouble
      | none => none
  | _ => none

/-- `PyComplex_AsCComplex`. `__complex__` comes first. -/
def asCComplex : SV → Option (Nat × Nat)
  | .cplx a b => some (a, b)
  | .obj { cplx := some r, .. } => okOf r
  | v => (asDouble v).map (·, 0)

def notFloat : PyExc := structErr "required argument is not a float"
def notComplex : PyExc := structErr "required argument is not a complex"

/-- `PyFloat_Pack2`, `Objects/floatobject.c:1894-2000`, on the magnitude `f = fn/fd`. -/
def pack2Round (sign : Nat) (fn fd e : Nat) : Py Nat :=
  -- `f *= 1024.0; bits = (unsigned short)f` and the round-to-even test
  let num := fn * 1024
  let bits := num / fd
  let rest := num - bits * fd
  let bits' := if 2 * rest > fd ∨ (2 * rest = fd ∧ bits % 2 = 1) then bits + 1 else bits
  if bits' = bits then .ok ((bits ||| (e * 1024)) ||| (sign * 32768))
  else if bits' = 1024 then
    if e + 1 = 31 then .error (.overflowError "float too large to pack with e format")
    else .ok ((e + 1) * 1024 ||| (sign * 32768))
  else .ok ((bits' ||| (e * 1024)) ||| (sign * 32768))

/-- The value of `PyFloat_Pack2` as a 16-bit pattern. -/
def pyFloatPack2Bits (x : Nat) : Py Nat :=
  let sign := f64.sign x
  if f64.expOf x = 0 ∧ f64.frac x = 0 then .ok (sign * 32768)
  else if f64.isInf x then .ok (0x1f * 1024 + sign * 32768)
  else if f64.isNaN x then
    let bits := (x &&& 0xffc0000000000) / 2 ^ 42
    let bits := if bits = 0 then bits ||| 512 else bits
    .ok (bits ||| 0x7c00 ||| (sign * 32768))
  else
    -- `f = frexp(x, &e)` then `f *= 2.0; e--`: `x = (m / 2^k) * 2^E` with `1 <= m/2^k < 2`
    let (m, e0) := f64.mag x
    let k := Nat.log2 m
    let E : Int := e0 + k
    if E ≥ 16 then .error (.overflowError "float too large to pack with e format")
    else if E < -25 then pack2Round sign 0 1 0
    else if E < -14 then
      -- `f = ldexp(f, 14 + e); e = 0`
      pack2Round sign m (2 ^ k * 2 ^ (-(14 + E)).toNat) 0
    else
      pack2Round sign (m - 2 ^ k) (2 ^ k) (E + 15).toNat

/-- `PyFloat_Pack4`, `Objects/floatobject.c@3.14.7:2180-2243`: a 32-bit pattern. -/
def pyFloatPack4Bits (x : Nat) : Py Nat :=
  let y := castDoubleToFloat x
  if f32.isInf y && !f64.isInf x then
    .error (.overflowError "float too large to pack with f format")
  else if f64.isNaN x then
    if x &&& (2 ^ 51) = 0 then
      if y &&& 0x3fffff ≠ 0 then .ok (y - 2 ^ 22) else .ok y
    else .ok y
  else .ok y

/-- `PyFloat_Unpack2`, `Objects/floatobject.c:2089-2143`. -/
def pyFloatUnpack2Bits (h : Nat) : Nat :=
  let sign := h / 32768 % 2
  let e := h / 1024 % 32
  let f := h % 1024
  if e = 0x1f then
    if f = 0 then f64.infBits sign
    else f64.infBits sign + f * 2 ^ 42
  else
    -- `x = f / 1024.0` (`+ 1.0` for normals) and `ldexp`; always exact in binary64
    let (m, ex) : Nat × Int := if e = 0 then (f, -24) else (f + 1024, (e : Int) - 25)
    (f64.encodeRounded sign m ex).getD 0

/-- `PyFloat_Unpack4`, `Objects/floatobject.c@3.14.7:2494-2545`. -/
def pyFloatUnpack4Bits (y : Nat) : Nat :=
  let x := castFloatToDouble y
  if f32.isNaN y ∧ y &&& 2 ^ 22 = 0 then x - 2 ^ 51 else x

/-- Bytes of a pattern of `n` bytes with the requested order. -/
def ordered (le : Bool) (n v : Nat) : List Nat :=
  if le then leBytes n v else (leBytes n v).reverse

/-- `pack_halffloat`, `Modules/_struct.c:275-288`. -/
def packHalffloat (v : SV) (le : Bool) : Py (List Nat) :=
  match asDouble v with
  | none => .error notFloat
  | some x => do return ordered le 2 (← pyFloatPack2Bits x)

def packFloatStd (v : SV) (le : Bool) : Py (List Nat) :=
  match asDouble v with
  | none => .error notFloat
  | some x => do return ordered le 4 (← pyFloatPack4Bits x)

def packDoubleStd (v : SV) (le : Bool) : Py (List Nat) :=
  match asDouble v with
  | none => .error notFloat
  | some x => .ok (ordered le 8 x)

/-- `bp_float_complex`/`lp_float_complex`, `Modules/_struct.c:1131-1144`. -/
def packFCStd (v : SV) (le : Bool) : Py (List Nat) :=
  match asCComplex v with
  | none => .error notComplex
  | some (a, b) => do
    let x ← pyFloatPack4Bits a
    let y ← pyFloatPack4Bits b
    return ordered le 4 x ++ ordered le 4 y

/-- `bp_double_complex`/`lp_double_complex`, `Modules/_struct.c:1146-1159`. -/
def packDCStd (v : SV) (le : Bool) : Py (List Nat) :=
  match asCComplex v with
  | none => .error notComplex
  | some (a, b) => .ok (ordered le 8 a ++ ordered le 8 b)

/-- `bp_longlong`/`lp_longlong`, `_PyLong_AsByteArray` with `with_exceptions = 0`. -/
def packLonglongStd (f : FormatDef) (v : SV) (le : Bool) : Py (List Nat) := do
  let n ← getPylong v
  if n < longMin ∨ n > longMax then
    throw (structErr s!"'{f.format}' format requires {longMin} <= number <= {longMax}")
  return (if le then lpLoop 8 n else bpLoop 8 n)

def packUlonglongStd (f : FormatDef) (v : SV) (le : Bool) : Py (List Nat) := do
  let n ← getPylong v
  if n < 0 ∨ n > ulongMax then
    throw (structErr s!"'{f.format}' format requires 0 <= number <= {ulongMax}")
  return (if le then lpLoop 8 n else bpLoop 8 n)

/-- `bp_int`/`lp_int`, `Modules/_struct.c:998-1024, 1319-1345`. -/
def packIntStd (f : FormatDef) (v : SV) (le : Bool) : Py (List Nat) := do
  let x ← orRange f false (getLong v)
  let i := f.size
  if i ≠ 8 then
    if i = 2 ∧ (x < -32768 ∨ x > 32767) then throw (rangeError f false)
    else if i = 4 ∧ (x < -2147483648 ∨ x > 2147483647) then throw (rangeError f false)
  return (if le then lpLoop i x else bpLoop i x)

/-- `bp_uint`/`lp_uint`, `Modules/_struct.c:1026-1050, 1347-1371`. -/
def packUintStd (f : FormatDef) (v : SV) (le : Bool) : Py (List Nat) := do
  let x ← orRange f true (getUlong v)
  let i := f.size
  if i ≠ 8 then
    if x ≥ (2 ^ (i * 8) : Int) then throw (rangeError f true)
  return (if le then lpLoop i x else bpLoop i x)

/-- Dispatch `e->pack(state, res, v, e)`. -/
def runPack (f : FormatDef) (v : SV) : Py (List Nat) :=
  match f.pack with
  | .none => .error (.named "SystemError" "no pack routine")
  | .npByte => do npSigned f (-128) 127 (← orRange f false (getLong v))
  | .npUbyte => do npUnsigned f 255 (← orRange f true (getLong v))
  | .npChar =>
    match v with
    | .bytes [b] => .ok [b]
    | _ => .error (structErr "char format requires a bytes object of length 1")
  | .npShort => do npSigned f (-32768) 32767 (← orRange f false (getLong v))
  | .npUshort => do npUnsigned f 65535 (← orRange f true (getLong v))
  | .npInt => do npSigned f (-2147483648) 2147483647 (← orRange f false (getLong v))
  | .npUint => do npUnsigned f 4294967295 (← orRange f true (getUlong v))
  | .npLong => do return twos 8 (← orRange f false (getLong v))
  | .npUlong => do return twos 8 (← orRange f true (getUlong v))
  | .npSsizeT => do return twos 8 (← orRange f false (getSsizeT v))
  | .npSizeT => do return twos 8 (← orRange f true (getSizeT v))
  | .npLonglong =>
    match getLonglong v with
    | .error (.overflowError _) =>
      .error (structErr s!"'{f.format}' format requires {longMin} <= number <= {longMax}")
    | .error e => .error e
    | .ok x => .ok (twos 8 x)
  | .npUlonglong =>
    match getUlonglong v with
    | .error (.overflowError _) =>
      .error (structErr s!"'{f.format}' format requires 0 <= number <= {ulongMax}")
    | .error e => .error e
    | .ok x => .ok (twos 8 x)
  | .npBool => do return [if (← isTrue v) then 1 else 0]
  | .npHalffloat => packHalffloat v true
  | .npFloat => packFloatStd v true
  | .npDouble => packDoubleStd v true
  | .npFloatComplex =>
    -- `Modules/_struct.c:792-800`: the C casts `(float)c.real`, `(float)c.imag`
    match asCComplex v with
    | none => .error notComplex
    | some (a, b) => .ok (leBytes 4 (castDoubleToFloat a) ++ leBytes 4 (castDoubleToFloat b))
  | .npDoubleComplex =>
    match asCComplex v with
    | none => .error notComplex
    | some (a, b) => .ok (leBytes 8 a ++ leBytes 8 b)
  | .npVoidP => do
    -- `np_void_p`, `Modules/_struct.c:820-835`, `PyLong_AsVoidPtr` (`Objects/longobject.c`)
    let n ← getPylong v
    if n < 0 then
      return twos 8 (← asC longMin longMax "Python int too large to convert to C long" n)
    else
      return twos 8 (← asC 0 ulongMax "Python int too large to convert to C unsigned long" n)
  | .bpInt => packIntStd f v false
  | .bpUint => packUintStd f v false
  | .bpLonglong => packLonglongStd f v false
  | .bpUlonglong => packUlonglongStd f v false
  | .bpBool => do return [if (← isTrue v) then 1 else 0]
  | .bpHalffloat => packHalffloat v false
  | .bpFloat => packFloatStd v false
  | .bpDouble => packDoubleStd v false
  | .bpFloatComplex => packFCStd v false
  | .bpDoubleComplex => packDCStd v false
  | .lpInt => packIntStd f v true
  | .lpUint => packUintStd f v true
  | .lpLonglong => packLonglongStd f v true
  | .lpUlonglong => packUlonglongStd f v true
  | .lpHalffloat => packHalffloat v true
  | .lpFloat => packFloatStd v true
  | .lpDouble => packDoubleStd v true
  | .lpFloatComplex => packFCStd v true
  | .lpDoubleComplex => packDCStd v true

/-- `x = (x ^ m) - m` then `x & m ? -1 - (long)(~x) : (long)x` of `bu_short`, `bu_int`,
`bu_longlong`, `lu_*`: sign extension of a `2 * m`-range value in 64-bit unsigned
arithmetic (`Modules/_struct.c:881-882, 895-896, 924-926`). -/
def signExtC (m x : Nat) : Int :=
  let w := 2 ^ 64
  let y := ((x ^^^ m) + w - m) % w
  if y &&& m ≠ 0 then -1 - ((w - 1 - y : Nat) : Int) else (y : Int)

/-- Signed value of a little-endian two's-complement image (`memcpy` into a C int). -/
def signedOf (size : Nat) (x : Nat) : Int :=
  if x ≥ 2 ^ (size * 8 - 1) then (x : Int) - 2 ^ (size * 8) else x

/-- Dispatch `e->unpack(state, res, e)` on the bytes starting at `res`. -/
def runUnpack (f : FormatDef) (p : List Nat) : Py SV :=
  let b := p.take f.size
  let le4 (o : Nat) := leVal ((p.drop o).take 4)
  let le8 (o : Nat) := leVal ((p.drop o).take 8)
  let be4 (o : Nat) := beVal ((p.drop o).take 4)
  let be8 (o : Nat) := beVal ((p.drop o).take 8)
  match f.unpack with
  | .none => .error (.named "SystemError" "no unpack routine")
  | .nuChar => .ok (.bytes (p.take 1))
  | .nuByte => .ok (.int (signedOf 1 (leVal b)))
  | .nuUbyte | .nuUshort | .nuUint | .nuUlong | .nuSizeT | .nuUlonglong =>
    .ok (.int (leVal b))
  | .nuShort | .nuInt | .nuLong | .nuSsizeT | .nuLonglong =>
    .ok (.int (signedOf f.size (leVal b)))
  | .nuVoidP => .ok (.int (leVal b))
  | .nuBool => .ok (.bool (p.head? != some 0))
  | .nuHalffloat => .ok (.float (pyFloatUnpack2Bits (leVal b)))
  | .nuFloat => .ok (.float (castFloatToDouble (leVal b)))
  | .nuDouble => .ok (.float (leVal b))
  | .nuFloatComplex => .ok (.cplx (castFloatToDouble (le4 0)) (castFloatToDouble (le4 4)))
  | .nuDoubleComplex => .ok (.cplx (le8 0) (le8 8))
  | .buShort => .ok (.int (signExtC 0x8000 (beVal b)))
  | .buInt => .ok (.int (signExtC 0x80000000 (beVal b)))
  | .buUint | .buUlonglong => .ok (.int (beVal b))
  | .buLonglong => .ok (.int (signExtC 0x8000000000000000 (beVal b)))
  | .buBool => .ok (.bool (p.head? != some 0))
  | .buHalffloat => .ok (.float (pyFloatUnpack2Bits (beVal b)))
  | .buFloat => .ok (.float (pyFloatUnpack4Bits (beVal b)))
  | .buDouble => .ok (.float (beVal b))
  | .buFloatComplex => .ok (.cplx (pyFloatUnpack4Bits (be4 0)) (pyFloatUnpack4Bits (be4 4)))
  | .buDoubleComplex => .ok (.cplx (be8 0) (be8 8))
  | .luShort => .ok (.int (signExtC 0x8000 (leVal b)))
  | .luInt => .ok (.int (signExtC 0x80000000 (leVal b)))
  | .luUint | .luUlonglong => .ok (.int (leVal b))
  | .luLonglong => .ok (.int (signExtC 0x8000000000000000 (leVal b)))
  | .luHalffloat => .ok (.float (pyFloatUnpack2Bits (leVal b)))
  | .luFloat => .ok (.float (pyFloatUnpack4Bits (leVal b)))
  | .luDouble => .ok (.float (leVal b))
  | .luFloatComplex => .ok (.cplx (pyFloatUnpack4Bits (le4 0)) (pyFloatUnpack4Bits (le4 4)))
  | .luDoubleComplex => .ok (.cplx (le8 0) (le8 8))

/-- Write `w` over `buf` starting at index `i`. -/
def overlay (buf : List Nat) (i : Nat) (w : List Nat) : List Nat :=
  buf.take i ++ w ++ buf.drop (i + w.length)

/-- One `while (j--)` turn of `s_unpack_internal`, `Modules/_struct.c@3.14.7:1884-1900`. -/
def unpackOne (code : Code) (res : List Nat) : Py SV :=
  let e := code.fmtdef
  if e.format = 's' then .ok (.bytes (res.take code.size))
  else if e.format = 'p' then
    let n :=
      if code.size = 0 then 0
      else
        let n := res.headD 0
        if n ≥ code.size then code.size - 1 else n
    .ok (.bytes ((res.drop 1).take n))
  else runUnpack e res

/-- `while (j--)` with a running `res`. -/
def unpackRepeat (code : Code) (buf : List Nat) : (j : Nat) → (off : Nat) → Py (List SV)
  | 0, _ => .ok []
  | j + 1, off => do
    let v ← unpackOne code (buf.drop off)
    let vs ← unpackRepeat code buf j (off + code.size)
    return v :: vs

/-- `s_unpack_internal`, `Modules/_struct.c:2038-2081`. -/
def sUnpackInternal (s : SObj) (buf : List Nat) : Py (List SV) :=
  s.codes.foldlM (init := []) fun acc code => do
    return acc ++ (← unpackRepeat code buf code.repeat_ code.offset)

/-- `Struct_unpack_impl`, `Modules/_struct.c:2105-2118`. -/
def structUnpack (s : SObj) (buf : List Nat) : Py (List SV) :=
  if buf.length ≠ s.sSize then
    .error (structErr s!"unpack requires a buffer of {s.sSize} bytes")
  else sUnpackInternal s buf

/-- The clinic `Py_ssize_t` argument conversion. -/
def ssizeArg (n : Int) : Py Int :=
  if n < longMin ∨ n > longMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok n

/-- `Struct_unpack_from_impl`, `Modules/_struct.c:2134-2173`. -/
def structUnpackFrom (s : SObj) (buf : List Nat) (offset0 : Int) : Py (List SV) := do
  let offset ← ssizeArg offset0
  let len : Int := buf.length
  let size : Int := s.sSize
  let offset ←
    if offset < 0 then
      if offset + size > 0 then
        Except.error (structErr
          s!"not enough data to unpack {size} bytes at offset {offset}")
      if offset + len < 0 then
        Except.error (structErr s!"offset {offset} out of range for {len}-byte buffer")
      pure (offset + len)
    else pure offset
  if len - offset < size then
    throw (structErr s!"unpack_from requires a buffer of at least {size + offset} bytes for \
      unpacking {size} bytes at offset {offset} (actual buffer size is {len})")
  sUnpackInternal s (buf.drop offset.toNat)

/-- `Struct_iter_unpack_impl` and `unpackiter_iternext`, `Modules/_struct.c:2231-2251,
2122-2154`: the tuples the iterator yields. `fuel` bounds the loop. -/
def iterLoop (s : SObj) (buf : List Nat) : (fuel : Nat) → (index : Nat) → Py (List (List SV))
  | 0, _ => .error .modelFuel
  | fuel + 1, index =>
    if index ≥ buf.length then .ok []
    else do
      let r ← sUnpackInternal s (buf.drop index)
      let rs ← iterLoop s buf fuel (index + s.sSize)
      return r :: rs

def structIterUnpack (s : SObj) (buf : List Nat) : Py (List (List SV)) :=
  if s.sSize = 0 then
    .error (structErr "cannot iteratively unpack with a struct of length 0")
  else if buf.length % s.sSize ≠ 0 then
    .error (structErr s!"iterative unpacking requires a buffer of a multiple of {s.sSize} bytes")
  else iterLoop s buf (buf.length + 1) 0

/-- `unpackiter_len`, `Modules/_struct.c:2211-2223`, on a live iterator. -/
def unpackiterLen (s : SObj) (buf : List Nat) (index : Nat) : Nat :=
  (buf.length - index) / s.sSize

/-- The `'s'` branch of `s_pack_internal`, `Modules/_struct.c@3.14.7:2184-2205`; the slot
`res` of `code.size` bytes comes in and goes out. -/
def packS (code : Code) (v : SV) (res : List Nat) : Py (List Nat) :=
  let p? := match v with | .bytes b | .bytearray b => some b | _ => none
  match p? with
  | none => .error (structErr "argument for 's' must be a bytes object")
  | some p =>
    let n := if p.length > code.size then code.size else p.length
    .ok (p.take n ++ res.drop n)

/-- The `'p'` branch, `Modules/_struct.c@3.14.7:2206-2234`: the count byte is written even for
a zero-sized field, where it lands on the first byte after the field. -/
def packP (code : Code) (v : SV) (res : List Nat) : Py (List Nat) :=
  let p? := match v with | .bytes b | .bytearray b => some b | _ => none
  match p? with
  | none => .error (structErr "argument for 'p' must be a bytes object")
  | some p =>
    let n := if code.size = 0 then 0
      else if p.length > code.size - 1 then code.size - 1 else p.length
    let body := res.take 1 ++ p.take n ++ res.drop (1 + n)
    let cnt := if n > 255 then 255 else n
    .ok (body.set 0 cnt)

/-- `e->pack` and the `OverflowError` rewrite of `Modules/_struct.c:2402-2407`. -/
def packCall (e : FormatDef) (v : SV) : Py (List Nat) :=
  match runPack e v, v with
  | .error (.overflowError _), .int _ => .error (structErr "int too large to convert")
  | r, _ => r

/-- Did the conversion of this value call `Struct.__init__`? -/
def SV.reinits : SV → Bool
  | .obj o => o.reinit
  | _ => false

/-- One `while (j--)` turn of `s_pack_internal`: the whole buffer is threaded because
`'p'` may write past its field. -/
def packOne (code : Code) (buf : List Nat) (off : Nat) (v : SV) : Py (List Nat) :=
  let e := code.fmtdef
  if e.format = 's' then do
    let w ← packS code v ((buf.drop off).take code.size)
    return overlay buf off w
  else if e.format = 'p' then do
    let w ← packP code v ((buf.drop off).take (max code.size 1))
    return overlay buf off w
  else do
    let w ← packCall e v
    -- `res += code->size` and `code++` read the array a re-entrant `__init__` freed
    if v.reinits then throw MEMORY
    return overlay buf off w

/-- `while (j--)` of `s_pack_internal`; the result is the buffer and the unused args. -/
def packRepeat (code : Code) : (j : Nat) → (off : Nat) → List Nat → List SV →
    Py (List Nat × List SV)
  | 0, _, buf, args => .ok (buf, args)
  | j + 1, off, buf, args =>
    match args with
    | [] => .error (.named "SystemError" "args exhausted")
    | v :: rest => do
      let buf' ← packOne code buf off v
      packRepeat code j (off + code.size) buf' rest

/-- `s_pack_internal`, `Modules/_struct.c:2331-2415`, working on the region starting at
the offset inside `buf`. -/
def sPackInternal (s : SObj) (buf : List Nat) (args : List SV) : Py (List Nat) := do
  let cleared := List.replicate s.sSize 0 ++ buf.drop s.sSize
  let r ← s.codes.foldlM (init := (cleared, args)) fun acc code =>
    packRepeat code code.repeat_ code.offset acc.1 acc.2
  return r.1

/-- `s_pack`, `Modules/_struct.c:2430-2459`. -/
def structPack (s : SObj) (args : List SV) : Py (List Nat) :=
  if args.length ≠ s.sLen then
    .error (structErr s!"pack expected {s.sLen} items for packing (got {args.length})")
  else
    -- one byte more than `s_size`: a trailing `0p` field writes to `_PyBytesWriter`'s
    -- slack, which `Finish` cuts off
    do return (← sPackInternal s (List.replicate (s.sSize + 1) 0) args).take s.sSize

/-- `PyNumber_AsSsize_t(args[1], PyExc_IndexError)`: the message names the type of the argument, not
of what `__index__` returned. -/
def asSsizeIndex (n : Int) (ty : String := "int") : Py Int :=
  if n < longMin ∨ n > longMax then
    .error (.indexError s!"cannot fit '{ty}' into an index-sized integer")
  else .ok n

/-- `s_pack_into`, `Modules/_struct.c:2478-2539`: the buffer afterwards. -/
def packIntoBody (s : SObj) (buffer : List Nat) (offset : Int) (args : List SV) :
    Py (List Nat) := do
  let len : Int := buffer.length
  let size : Int := s.sSize
  let offset ←
    if offset < 0 then
      if offset + size > 0 then
        Except.error (structErr s!"no space to pack {size} bytes at offset {offset}")
      if offset + len < 0 then
        Except.error (structErr s!"offset {offset} out of range for {len}-byte buffer")
      pure (offset + len)
    else pure offset
  if len - offset < size then
    throw (structErr s!"pack_into requires a buffer of at least {size + offset} bytes for \
      packing {size} bytes at offset {offset} (actual buffer size is {len})")
  let o := offset.toNat
  let tail ← sPackInternal s (buffer.drop o) args
  -- `.take`: a `0p` count byte past the end of the buffer is not part of the object
  return (buffer.take o ++ tail).take buffer.length

def structPackInto (s : SObj) (buffer : List Nat) (offset0 : Int) (args : List SV) :
    Py (List Nat) := do
  if args.length ≠ s.sLen then
    throw (structErr s!"pack_into expected {s.sLen} items for packing (got {args.length})")
  packIntoBody s buffer (← asSsizeIndex offset0) args

/-- A buffer argument. `raises` is an object whose `__buffer__` raises. -/
inductive BufArg where
  | bytes (b : List Nat)
  | bytearray (b : List Nat)
  | notBuffer (ty : String)
  | raises (ty : String) (e : PyExc)
  deriving Repr, DecidableEq, Inhabited

/-- `y*`, and `PyObject_GetBuffer` with `PyBUF_SIMPLE`: a raising `__buffer__` passes through. -/
def readBuf : BufArg → Py (List Nat)
  | .bytes b | .bytearray b => .ok b
  | .notBuffer t => .error (.typeError s!"a bytes-like object is required, not '{t}'")
  | .raises _ e => .error e

/-- `w*`, `Modules/_struct.c@3.14.7:2335`: any failure, a raising `__buffer__` too, is this `TypeError`. -/
def writeBuf : BufArg → Py (List Nat)
  | .bytearray b => .ok b
  | .bytes _ => .error (.typeError "argument must be read-write bytes-like object, not bytes")
  | .notBuffer t | .raises t _ =>
    .error (.typeError s!"argument must be read-write bytes-like object, not {t}")

/-- An offset argument. `index` is an object with `__index__`, which may also call `__init__` on the
`Struct`; `none` means it does not. -/
inductive OffArg where
  | int (n : Int)
  | index (ty : String) (r : Py Int) (reinit : Option SObj)
  | notIndex (ty : String)
  deriving Inhabited

/-- The type name of an offset. -/
def OffArg.ty : OffArg → String
  | .int _ => "int"
  | .index t _ _ => t
  | .notIndex t => t

/-- `_PyNumber_Index`. -/
def offNumber : OffArg → Py Int
  | .int n => .ok n
  | .index _ r _ => r
  | .notIndex t => .error (.typeError s!"'{t}' object cannot be interpreted as an integer")

/-- The clinic `Py_ssize_t` argument of `unpack_from`. -/
def offSsize (a : OffArg) : Py Int := do ssizeArg (← offNumber a)

/-- `Struct_unpack_impl`: the clinic takes the buffer first. -/
def structUnpackA (s : SObj) (b : BufArg) : Py (List SV) := do
  structUnpack s (← readBuf b)

/-- `Struct_unpack_from_impl`: the clinic takes the buffer, then the offset. -/
def structUnpackFromA (s : SObj) (b : BufArg) (off : OffArg) : Py (List SV) := do
  let buf ← readBuf b
  structUnpackFrom s buf (← offSsize off)

/-- The arguments of `s_pack_into`. -/
inductive PackIntoArgs where
  | noBuffer
  | noOffset
  | full (b : BufArg) (off : OffArg) (args : List SV)
  deriving Inhabited

/-- `s_pack_into`, `Modules/_struct.c:2478-2539`, with the `Struct` as it is once the offset has been
converted. `nargs` is checked against the `s_len` from before that conversion, so a longer format
installed by `__index__` makes `s_pack_internal` read past `args`. -/
def structPackIntoA (s : SObj) : PackIntoArgs → Py (List Nat)
  | .noBuffer => .error (structErr "pack_into expected buffer argument")
  | .noOffset => .error (structErr "pack_into expected offset argument")
  | .full b off args =>
    if args.length ≠ s.sLen then
      .error (structErr s!"pack_into expected {s.sLen} items for packing (got {args.length})")
    else do
      let buffer ← writeBuf b
      let n ← offNumber off
      let offset ← asSsizeIndex n off.ty
      let s' := match off with
        | .index _ _ (some t) => t
        | _ => s
      if args.length < s'.sLen then throw MEMORY
      packIntoBody s' buffer offset args

/-- A `struct.unpack_iterator`: `so` is `NULL` once exhausted. The `Struct` is a shared object, so its
current state is passed in. -/
structure UIter where
  live : Bool := true
  buf : List Nat
  index : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- `Struct_iter_unpack_impl`, `Modules/_struct.c:2285-2318`. -/
def structIterUnpackA (s : SObj) (b : BufArg) : Py UIter :=
  if s.sSize = 0 then .error (structErr "cannot iteratively unpack with a struct of length 0")
  else
    match readBuf b with
    | .error e => .error e
    | .ok buf =>
      if buf.length % s.sSize ≠ 0 then
        .error (structErr s!"iterative unpacking requires a buffer of a multiple of {s.sSize} bytes")
      else .ok { buf }

/-- `unpackiter_iternext`, `Modules/_struct.c:2230-2251`: `none` is `StopIteration`. The bound on the
read is only an `assert`, against the `s_size` of the moment, which `__init__` can have changed. -/
def iterNextU (s : SObj) (it : UIter) : UIter × Py (Option (List SV)) :=
  if !it.live then (it, .ok none)
  else if it.index ≥ it.buf.length then ({ it with live := false }, .ok none)
  else if it.index + s.sSize > it.buf.length then (it, .error MEMORY)
  else
    match sUnpackInternal s (it.buf.drop it.index) with
    | .ok r => ({ it with index := it.index + s.sSize }, .ok (some r))
    | .error e => ({ it with index := it.index + s.sSize }, .error e)

/-- `unpackiter_len`, `Modules/_struct.c:2211-2223`: `/ s_size` is undefined when it is `0`, which
`__init__` can make it. -/
def iterLenU (s : SObj) (it : UIter) : Py Nat :=
  if !it.live then .ok 0
  else if s.sSize = 0 then .error MEMORY
  else .ok ((it.buf.length - it.index) / s.sSize)

/-- `list(iterator)`. -/
def iterDrive (s : SObj) : (fuel : Nat) → UIter → Py (List (List SV))
  | 0, _ => .error .modelFuel
  | fuel + 1, it =>
    match iterNextU s it with
    | (_, .error e) => .error e
    | (_, .ok none) => .ok []
    | (it', .ok (some r)) => do
      return r :: (← iterDrive s fuel it')

/-- `s_sizeof`, `Modules/_struct.c:2545-2555` (`_PyObject_SIZE` is 56). -/
def sSizeof (s : SObj) : Nat := 56 + 32 + 32 * s.codes.length

/-- `repr` of one character of an accepted format: the only non-printable ones are the
`Py_ISSPACE` characters, and a quote or backslash is never accepted. -/
def reprChar (c : Nat) : String :=
  if c = 10 then "\\n" else if c = 13 then "\\r" else if c = 9 then "\\t"
  else if c = 11 then "\\x0b" else if c = 12 then "\\x0c"
  else String.singleton (Char.ofNat c)

/-- `s_repr`, `Modules/_struct.c:2557-2563`: `"%s(%R)"` of the type name and the format. -/
def sRepr (s : SObj) : String :=
  "Struct('" ++ String.join (s.format.map reprChar) ++ "')"

/-- `Struct.format`, `s_get_format`, `Modules/_struct.c@3.14.7:2398-2405`. -/
def sGetFormat (s : SObj) : List Nat := s.format

/-- `s_new`, `Modules/_struct.c:1867-1951`: a `Struct` before `__init__` has no codes. -/
def sNew : Option SObj := none

/-- `ENSURE_STRUCT_IS_READY`, `Modules/_struct.c:2083-2090`. -/
def ensureReady (s : Option SObj) : Py SObj :=
  match s with
  | some s => .ok s
  | none => .error (.named "RuntimeError" "Struct object is not initialized")

/-- `s_get_size`, `Modules/_struct.c@3.14.7:2407-2412`: `s_new` stores -1, and this getter is
the one accessor without `ENSURE_STRUCT_IS_READY`. -/
def sGetSize : Option SObj → Int
  | some s => s.sSize
  | none => -1

/-- `calcsize_impl`, `Modules/_struct.c:2689-2694`. -/
def calcsize (f : FmtArg) : Py Nat := do return (← cacheStruct f).sSize

/-- `pack`, `Modules/_struct.c@3.14.7:2591-2609`. -/
def modPack (f : FmtArg) (args : List SV) : Py (List Nat) := do
  structPack (← cacheStruct f) args

/-- `pack_into`, `Modules/_struct.c:2734-2742`. -/
def modPackInto (f : FmtArg) (buf : List Nat) (off : Int) (args : List SV) : Py (List Nat) := do
  structPackInto (← cacheStruct f) buf off args

/-- `unpack_impl`, `Modules/_struct.c:2758-2763`. -/
def modUnpack (f : FmtArg) (buf : List Nat) : Py (List SV) := do
  structUnpack (← cacheStruct f) buf

/-- `unpack_from_impl`, `Modules/_struct.c:2781-2787`. -/
def modUnpackFrom (f : FmtArg) (buf : List Nat) (off : Int) : Py (List SV) := do
  structUnpackFrom (← cacheStruct f) buf off

/-- `iter_unpack_impl`, `Modules/_struct.c:2803-2809`. -/
def modIterUnpack (f : FmtArg) (buf : List Nat) : Py (List (List SV)) := do
  structIterUnpack (← cacheStruct f) buf

/-- `unpack_impl` with its arguments as objects: the clinic converts the format, then the buffer. -/
def modUnpackA (f : FmtArg) (b : BufArg) : Py (List SV) := do
  structUnpackA (← cacheStruct f) b

/-- `unpack_from_impl`: the format, then the buffer, then the offset. -/
def modUnpackFromA (f : FmtArg) (b : BufArg) (off : OffArg) : Py (List SV) := do
  structUnpackFromA (← cacheStruct f) b off

/-- `iter_unpack_impl`, whose buffer is an `object` that `Struct_iter_unpack_impl` converts. -/
def modIterUnpackA (f : FmtArg) (b : BufArg) : Py UIter := do
  structIterUnpackA (← cacheStruct f) b

/-- `pack`, `Modules/_struct.c@3.14.7:2591-2609`: the format is the first of `*args`. -/
def modPackA : List SV → Option FmtArg → Py (List Nat)
  | _, none => .error (.typeError "missing format argument")
  | args, some f => do structPack (← cacheStruct f) args

/-- `pack_into`, `Modules/_struct.c:2734-2742`. -/
def modPackIntoA : PackIntoArgs → Option FmtArg → Py (List Nat)
  | _, none => .error (.typeError "missing format argument")
  | a, some f => do structPackIntoA (← cacheStruct f) a

end PyLean.TextLibs.Struct
