import PyLean.UnicodeObj.ObjectWriter

/-!
`PyUnicode_FromFormat` and `PyUnicodeWriter_Format`: Objects/unicodeobject.c:2576-3217.

`va_arg` is a list of `VArg`. Asking for an argument of the wrong type is undefined behaviour by
the C standard, so the model gives `.modelFuel` for it, and the difftest never does it. Sizes are
those of LP64: `int` has 32 bits, everything else here 64.

Three things are not modelled. Allocation failure, which is what `MemoryError` from a huge width
comes to. The signed overflow of `precision + sign` at unicodeobject.c:2882, which needs a precision
of exactly `PY_SSIZE_T_MAX` and a negative number, and which ended in the same `MemoryError` as its
neighbours when probed. And `writer->overallocate`, which decides how much memory is held; it does
send a first write of the last chunk through the `readonly` branches of
`_PyUnicodeWriter_WriteStr` and `_WriteASCIIString`, which keep a reference to the string instead
of copying it, with the same text and the same capacity.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The name of a type, as `_PyType_GetFullyQualifiedName` sees it. -/
inductive TName where
  /-- A static type: its `tp_name`, as it is. -/
  | static (tpName : Str)
  /-- A heap type: `__module__`, `none` if it is not a `str`, and `__qualname__`. -/
  | heap (module : Option Str) (qualname : Str)

/-- `_PyType_GetFullyQualifiedName(type, sep)`, Objects/typeobject.c. -/
def typeFullName (sep : Nat) : TName → Str
  | .static n => n
  | .heap (some m) q =>
    if m = lit "builtins" ∨ m = lit "__main__" then q else m ++ [sep] ++ q
  | .heap none q => q

/-- An argument of the `...`. -/
inductive VArg where
  /-- Any C integer type; `va_arg` takes as many bits as the conversion asks for. -/
  | int (v : Int)
  | obj (o : GObj)
  /-- `NULL` for the object of `%V`. -/
  | nullObj
  | cstr (b : Bytes)
  | wstr (s : Str)
  | ptr (v : Nat)
  /-- A type object, for `%N`. -/
  | type (t : TName)
  /-- An object of a type with this name, for `%T`. -/
  | inst (t : TName)

/-- `va_arg` of the wrong type. -/
def vaError {α : Type} : Py α := .error .modelFuel

def popInt : List VArg → Py (Int × List VArg)
  | .int v :: t => .ok (v, t)
  | _ => vaError

/-- A marker, not a Python exception: `_PyUnicode_FastCopyCharacters` was reached with a negative
count, which is `memcpy` with a huge `size_t`, followed by `writer->pos += length`. -/
def negCopy : PyExc := .named "<memcpy with a negative length>" ""

/-- The part of a conversion specification before the conversion character. -/
structure FSpec where
  ljust : Bool := false
  zero : Bool := false
  alt : Bool := false
  width : Int := -1
  precision : Int := -1
  sizemod : Nat := 0
  deriving Repr, DecidableEq

def F_LONG : Nat := 1
def F_LONGLONG : Nat := 2
def F_SIZE : Nat := 3
def F_PTRDIFF : Nat := 4
def F_INTMAX : Nat := 5

/-- The character at `f`, with the NUL at the end of the format. -/
def ffChar : List Nat → Nat
  | [] => 0
  | c :: _ => c

def isDigitC (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- The flags, unicodeobject.c:2722-2730. -/
def ffParseFlags (s : FSpec) : List Nat → FSpec × List Nat
  | [] => (s, [])
  | c :: t =>
    if c = 45 then ffParseFlags { s with ljust := true } t
    else if c = 48 then ffParseFlags { s with zero := true } t
    else if c = 35 then ffParseFlags { s with alt := true } t
    else (s, c :: t)

/-- The digits of a width or a precision after the first, with the check before each step. -/
def digitLoop (msg : String) (v : Int) : List Nat → Py (Int × List Nat)
  | [] => .ok (v, [])
  | c :: t =>
    if isDigitC c then
      if v > (ssizeMax - ((c : Int) - 48)) / 10 then .error (.valueError msg)
      else digitLoop msg (v * 10 + ((c : Int) - 48)) t
    else .ok (v, c :: t)

/-- unicodeobject.c:2733-2754. -/
def ffParseWidth (s : FSpec) (f : List Nat) (args : List VArg) :
    Py (FSpec × List Nat × List VArg) :=
  match f with
  | 42 :: t => do
    let (v, args') ← popInt args
    if v < 0 then .ok ({ s with ljust := true, width := -v }, t, args')
    else .ok ({ s with width := v }, t, args')
  | c :: t =>
    if isDigitC c then do
      let (v, t') ← digitLoop "width too big" ((c : Int) - 48) t
      .ok ({ s with width := v }, t', args)
    else .ok (s, c :: t, args)
  | [] => .ok (s, [], args)

/-- unicodeobject.c:2755-2778. A negative `*` becomes -2, and `.` alone leaves -1. -/
def ffParsePrecision (s : FSpec) (f : List Nat) (args : List VArg) :
    Py (FSpec × List Nat × List VArg) :=
  match f with
  | 46 :: 42 :: t => do
    let (v, args') ← popInt args
    .ok ({ s with precision := if v < 0 then -2 else v }, t, args')
  | 46 :: c :: t =>
    if isDigitC c then do
      let (v, t') ← digitLoop "precision too big" ((c : Int) - 48) t
      .ok ({ s with precision := v }, t', args)
    else .ok (s, c :: t, args)
  | [46] => .ok (s, [], args)
  | f => .ok (s, f, args)

/-- unicodeobject.c:2780-2802. -/
def parseSizemod : List Nat → Nat × List Nat
  | 108 :: 108 :: t => (F_LONGLONG, t)
  | 108 :: t => (F_LONG, t)
  | 122 :: t => (F_SIZE, t)
  | 116 :: t => (F_PTRDIFF, t)
  | 106 :: t => (F_INTMAX, t)
  | f => (0, f)

/-- Everything before the conversion character. -/
def parseSpec (f : List Nat) (args : List VArg) : Py (FSpec × List Nat × List VArg) := do
  let (s, f1) := ffParseFlags {} f
  let (s, f2, args) ← ffParseWidth s f1 args
  let (s, f3, args) ← ffParsePrecision s f2 args
  let (sizemod, f4) := parseSizemod f3
  .ok ({ s with sizemod }, f4, args)

/-- `unicode_fromformat_write_str`, unicodeobject.c:2577-2620. `length` goes negative for a
precision of -2, and the copy at line 2701 does not look. -/
def fmtWriteStr (w : UWriter) (str : Str) (width precision : Int) (ljust : Bool) : Py UWriter :=
  let total : Int := str.length
  if (precision = -1 ∨ precision ≥ total) ∧ width ≤ total then .ok (writeText w str)
  else
    let length : Int := if precision ≠ -1 then min precision total else total
    if length < 0 then .error negCopy
    else
      let part := str.take length.toNat
      let arglen := max length width
      let maxchar := if capOf (canonicalKind str) > w.cap then maxCharOf part else w.cap
      let cap := if arglen = 0 then w.cap else prepareCap w.cap maxchar
      let spaces := List.replicate (max (width - length) 0).toNat 32
      .ok { text := w.text ++ (if ljust then part ++ spaces else spaces ++ part), cap }

/-- The C string: up to the first NUL. -/
def cstrOf (b : Bytes) : Bytes := b.takeWhile (· != 0)

/-- `while (length < precision && str[length]) length++`, for the string up to its NUL. -/
def boundedLen (s : List Nat) (precision : Int) : Nat :=
  if precision ≤ 0 then 0 else min precision.toNat s.length

/-- `unicode_fromformat_write_utf8`, unicodeobject.c:2623-2661. `*consumed` is asked for when the
precision stopped the scan, which truncates a trailing incomplete sequence. -/
def fmtWriteUtf8 (w : UWriter) (str : Bytes) (width precision : Int) (ljust : Bool) :
    Py UWriter := do
  let s := cstrOf str
  let (length, stateful) :=
    if precision = -1 then (s.length, false)
    else
      let l := boundedLen s precision
      (l, decide ((l : Int) = precision))
  let bytes := s.take length
  if width < 0 then
    let (w', r) := decodeWriter w bytes .replace stateful
    let _ ← r
    .ok w'
  else
    let unicode ← if stateful then (·.1) <$> utf8DecodeStateful bytes .replace
      else utf8Decode bytes .replace
    fmtWriteStr w unicode width (-1) ljust

/-- `unicode_fromformat_write_wcstr`, unicodeobject.c:2664-2690. -/
def fmtWriteWcstr (w : UWriter) (str : Str) (width precision : Int) (ljust : Bool) :
    Py UWriter := do
  let s := str.takeWhile (· != 0)
  let length := if precision = -1 then s.length else boundedLen s precision
  let part := s.take length
  if width < 0 then
    let (w', r) := writeWide w part length
    let _ ← r
    .ok w'
  else
    if part.isEmpty then fmtWriteStr w [] width (-1) ljust
    else
      let _ ← findMaxcharSurrogates part 0
      fmtWriteStr w part width (-1) ljust

/-- `v` as C reads it: `bits` bits, two's complement. -/
def wrapU (bits : Nat) (v : Int) : Nat := (v % (2 ^ bits : Int)).toNat

def wrapS (bits : Nat) (v : Int) : Int :=
  let u := wrapU bits v
  if u ≥ 2 ^ (bits - 1) then (u : Int) - 2 ^ bits else u

def sizeBits (sizemod : Nat) : Nat := if sizemod = 0 then 32 else 64

/-- What `sprintf` leaves in `buffer`, unicodeobject.c:2855-2871. `%X` is `%x` in capitals. -/
def sprintInt (conv sizemod : Nat) (v : Int) : Str :=
  let bits := sizeBits sizemod
  let u := wrapU bits v
  if conv = 111 then digitsOf 8 u
  else if conv = 117 then digitsOf 10 u
  else if conv = 120 then digitsOf 16 u
  else if conv = 88 then (digitsOf 16 u).map fun c => if 97 ≤ c ∧ c ≤ 102 then c - 32 else c
  else
    let n := wrapS bits v
    (if n < 0 then [45] else []) ++ digitsOf 10 n.natAbs

/-- The layout of an integer, unicodeobject.c:2878-2919. -/
def intLayout (buffer : Str) (width0 precision0 : Int) (zero ljust : Bool) : Str :=
  let sign : Bool := buffer.head? == some 45
  let signN : Int := if sign then 1 else 0
  let digits := if sign then buffer.tail else buffer
  let len : Int := digits.length
  let precision1 := max precision0 len
  let width := max width0 (precision1 + signN)
  let precision := if zero && !ljust then width - signN else precision1
  let spacepad := (max (width - precision - signN) 0).toNat
  let zeropad := (max (precision - len) 0).toNat
  (if spacepad != 0 && !ljust then List.replicate spacepad 32 else []) ++
    (if sign then [45] else []) ++ List.replicate zeropad 48 ++ digits ++
    (if spacepad != 0 && ljust then List.replicate spacepad 32 else [])

/-- `sprintf("%p")` on glibc, which prints NULL as `(nil)`, then unicodeobject.c:2930-2939. -/
def pointerText (v : Nat) : Str :=
  let number := if v = 0 then lit "(nil)" else lit "0x" ++ digitsOf 16 v
  if number.getD 1 0 = 120 then number else lit "0x" ++ number

def invalidFormat (p : List Nat) : PyExc :=
  .named "SystemError" ("invalid format string: " ++ toLeanString p)

/-- The separator of `%#T` and `%#N`. -/
def typeSep (alt : Bool) : Nat := if alt then 58 else 46

/-- The first `switch`, unicodeobject.c:2806-2819: what a size modifier, a width or a precision may
go with. -/
def ffBad (s : FSpec) (c : Nat) : Bool :=
  if c = 100 ∨ c = 105 ∨ c = 111 ∨ c = 117 ∨ c = 120 ∨ c = 88 then false
  else if c = 99 ∨ c = 112 then s.sizemod != 0 || decide (s.width ≥ 0) || decide (s.precision ≥ 0)
  else if c = 115 ∨ c = 86 then s.sizemod != 0 && s.sizemod != F_LONG
  else s.sizemod != 0

/-- The second `switch`, unicodeobject.c:2821-3109. Returns the writer and what is left of the
arguments. `p` is the text of the specification, for the message. -/
def fromFormatSwitch (w : UWriter) (p : List Nat) (s : FSpec) (c : Nat) (args : List VArg) :
    Py (UWriter × List VArg) :=
  if c = 99 then
    match args with
    | .int v :: t =>
      let ordinal := wrapS 32 v
      if ordinal < 0 ∨ ordinal > maxUnicode then
        .error (.overflowError "character argument not in range(0x110000)")
      else .ok ({ text := w.text ++ [ordinal.toNat], cap := prepareCap w.cap ordinal.toNat }, t)
    | _ => vaError
  else if c = 100 ∨ c = 105 ∨ c = 111 ∨ c = 117 ∨ c = 120 ∨ c = 88 then
    match args with
    | .int v :: t =>
      .ok (writeAsciiText w (intLayout (sprintInt c s.sizemod v) s.width s.precision s.zero s.ljust), t)
    | _ => vaError
  else if c = 112 then
    match args with
    | .ptr v :: t => .ok (writeAsciiText w (pointerText v), t)
    | _ => vaError
  else if c = 115 then
    if s.sizemod != 0 then
      match args with
      | .wstr x :: t => do return (← fmtWriteWcstr w x s.width s.precision s.ljust, t)
      | _ => vaError
    else
      match args with
      | .cstr b :: t => do return (← fmtWriteUtf8 w b s.width s.precision s.ljust, t)
      | _ => vaError
  else if c = 85 then
    match args with
    | .obj (.str x) :: t => do return (← fmtWriteStr w x s.width s.precision s.ljust, t)
    | _ => vaError
  else if c = 86 then
    match args with
    | o :: alt :: t =>
      match o, alt with
      | .obj (.str x), _ => do return (← fmtWriteStr w x s.width s.precision s.ljust, t)
      | .nullObj, .wstr x =>
        if s.sizemod != 0 then do return (← fmtWriteWcstr w x s.width s.precision s.ljust, t)
        else vaError
      | .nullObj, .cstr b =>
        if s.sizemod = 0 then do return (← fmtWriteUtf8 w b s.width s.precision s.ljust, t)
        else vaError
      | _, _ => vaError
    | _ => vaError
  else if c = 83 ∨ c = 82 ∨ c = 65 then
    match args with
    | .obj o :: t => do
      let text ← if c = 83 then strG reprFuel o
        else if c = 82 then reprG reprFuel o else asciiG reprFuel o
      return (← fmtWriteStr w text s.width s.precision s.ljust, t)
    | _ => vaError
  else if c = 84 then
    match args with
    | .obj o :: t => do
      return (← fmtWriteStr w (lit o.tpName) s.width s.precision s.ljust, t)
    | .inst n :: t => do
      return (← fmtWriteStr w (typeFullName (typeSep s.alt) n) s.width s.precision s.ljust, t)
    | _ => vaError
  else if c = 78 then
    match args with
    | .type n :: t => do
      return (← fmtWriteStr w (typeFullName (typeSep s.alt) n) s.width s.precision s.ljust, t)
    | .obj _ :: _ => .error (.typeError "%N argument must be a type")
    | _ => vaError
  else .error (invalidFormat p)

/-- The conversion, from `f` at the conversion character. -/
def fromFormatConv (w : UWriter) (p : List Nat) (s : FSpec) (f : List Nat) (args : List VArg) :
    Py (UWriter × List VArg) :=
  if ffBad s (ffChar f) then .error (invalidFormat p)
  else fromFormatSwitch w p s (ffChar f) args

/-- `unicode_fromformat_arg`, unicodeobject.c:2699-3113, with `p` at the `%`. -/
def fromFormatArg (w : UWriter) (p : List Nat) (args : List VArg) :
    Py (UWriter × List Nat × List VArg) := do
  match p with
  | [] => .error .modelFuel
  | _ :: f0 =>
    if ffChar f0 = 37 then
      .ok ({ text := w.text ++ [37], cap := prepareCap w.cap 37 }, f0.tail, args)
    else
      let (s, f, args') ← parseSpec f0 args
      let (w', args'') ← fromFormatConv w p s f args'
      .ok (w', f.tail, args'')

/-- The loop of `unicode_from_format`, unicodeobject.c:3139-3160. A failure comes with the writer
as it stood, which `PyUnicodeWriter_Format` needs. -/
def fromFormatLoop : Nat → List Nat → List VArg → UWriter → UWriter × Py Unit
  | 0, _, _, w => (w, .error .modelFuel)
  | _ + 1, [], _, w => (w, .ok ())
  | fuel + 1, c :: t, args, w =>
    if c = 37 then
      match fromFormatArg w (c :: t) args with
      | .error e => (w, .error e)
      | .ok (w', f', args') => fromFormatLoop fuel f' args' w'
    else
      let chunk := (c :: t).takeWhile (· != 37)
      fromFormatLoop fuel ((c :: t).drop chunk.length) args (writeAsciiText w chunk)

/-- `0x%02x`. -/
def ffHex2 (b : Nat) : String := toLeanString (hexDigits 2 b)

/-- `unicode_from_format`, unicodeobject.c:3116-3167. -/
def unicodeFromFormat (w : UWriter) (format : Bytes) (args : List VArg) : UWriter × Py Unit :=
  let f := cstrOf format
  match f.find? (· > 127) with
  | some b =>
    (w, .error (.valueError ("PyUnicode_FromFormatV() expects an ASCII-encoded format string, " ++
      s!"got a non-ASCII byte: 0x{ffHex2 b}")))
  | none => fromFormatLoop (f.length + 1) f args w

/-- `PyUnicode_FromFormat`, unicodeobject.c:3170-3192. -/
def pyUnicodeFromFormat (format : Bytes) (args : List VArg) : Py (Str × Kind) :=
  let (w, r) := unicodeFromFormat {} format args
  match r with
  | .ok _ => .ok w.finish
  | .error e => .error e

/-- `PyUnicodeWriter_Format`, unicodeobject.c:3195-3217: `pos` is put back, and only `pos`. -/
def writerFormat (w : UWriter) (format : Bytes) (args : List VArg) : UWriter × Py Unit :=
  let (w', r) := unicodeFromFormat w format args
  match r with
  | .ok _ => (w', .ok ())
  | .error e => ({ w' with text := w.text }, .error e)

end PyLean.UnicodeObj
