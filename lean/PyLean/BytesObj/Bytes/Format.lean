import PyLean.BytesObj.Bytes.Writer

/-!
`bytes % args` and `bytearray % args`: `_PyBytes_FormatEx`, Objects/bytesobject.c:617-1167,
and its helpers `getnextarg`, `formatfloat`, `formatlong`, `byte_converter`,
`format_obj`, plus `_PyUnicode_FormatLong` (Objects/unicode_format.c:192-314),
which `formatlong` delegates to.

`pos` and `cnt` are the C variables `fmt - format` and `fmtcnt`; reading at `pos`
past the end is the NUL terminator of the bytes or bytearray.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- `F_LJUST`, `F_SIGN`, `F_BLANK`, `F_ALT`, `F_ZERO`, Include/internal/pycore_format.h. -/
structure Fl where
  ljust : Bool := false
  sign : Bool := false
  blank : Bool := false
  alt : Bool := false
  zero : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `INT_MAX`. -/
def intMax : Int := 2147483647

/-- Formatting state: `fmt`, `fmtcnt`, `res`, the writer, `args`, `arglen`, `argidx`, `key`. -/
structure FS where
  pos : Nat
  cnt : Int
  out : Seq
  w : Writer
  args : Obj
  arglen : Int
  argidx : Int
  key : Option Seq := none
  deriving Inhabited

/-! ## getnextarg, formatlong, formatfloat, byte_converter, format_obj -/

/-- The text of a byte string that is ASCII. -/
def seqText (s : Seq) : String := String.ofList (s.map Char.ofNat)

/-- `FORMAT_ERROR(EXC, FMT, ...)`, bytesobject.c:395-407, with the arguments formatted. `%R` of the
key is `repr`, whose own failure would replace the exception. -/
def formatError (exc : String → PyExc) (st : FS) (msg : String) : PyExc :=
  match st.key with
  | some k =>
    match bytesRepr k true with
    | .ok r => exc ("format argument " ++ seqText r ++ ": " ++ msg)
    | .error e => e
  | none =>
    if st.argidx ≥ 0 then exc ("format argument " ++ s!"{st.argidx}: " ++ msg)
    else exc ("format argument: " ++ msg)

/-- `getnextarg`, bytesobject.c:409-426. -/
def getNextArg (st : FS) (allowone : Bool) : Py (Obj × FS) :=
  let notEnough : PyExc :=
    .typeError s!"not enough arguments for format string (got {if st.arglen < 0 then 1 else st.arglen})"
  if st.argidx < st.arglen then
    let st' := { st with argidx := st.argidx + 1 }
    if st.arglen ≥ 0 then
      match st.args with
      | .tuple xs => .ok (xs.getD st.argidx.toNat default, st')
      | _ => .error (badInternalCall "PyTuple_GetItem")
    else if allowone then .ok (st.args, st')
    else .error notEnough
  else .error notEnough

/-- The base-marker removal and sign fix-up of `_PyUnicode_FormatLong`,
unicode_format.c:255-269: `buf + 2`, with `buf[0] = '-'` when negative. -/
def dropMarker (sign : Bool) (buf : Seq) : Seq :=
  if sign then 45 :: (buf.drop 3) else buf.drop 2

/-- The text manipulation of `_PyUnicode_FormatLong`, unicode_format.c:247-307,
on `result = PyNumber_ToBase(val, base)`. -/
def formatLongText (result : Seq) (alt : Bool) (prec : Int) (type : Nat) : Seq :=
  let isBased := type = 111 ∨ type = 120 ∨ type = 88
  let numnon₀ : Int := if isBased then 2 else 0
  let sign := result.headD 0 = 45
  let numnon₁ := numnon₀ + (if sign then 1 else 0)
  let numdigits : Int := (result.length : Int) - numnon₁
  -- Get rid of base marker unless F_ALT
  let stripped := !alt ∧ isBased
  let buf := if stripped then dropMarker sign result else result
  let numnondigits := if stripped then numnon₁ - 2 else numnon₁
  -- Fill with leading zeroes to meet minimum width
  let buf :=
    if prec > numdigits then
      buf.take numnondigits.toNat ++ List.replicate (prec - numdigits).toNat 48 ++
        buf.drop numnondigits.toNat
    else buf
  -- Fix up case for hex conversions
  if type = 88 then buf.map (fun c => if 97 ≤ c ∧ c ≤ 120 then c - 32 else c) else buf

/-- The base of a conversion, unicode_format.c:211-228. -/
def longBase (type : Nat) : Nat :=
  if type = 111 then 8 else if type = 120 ∨ type = 88 then 16 else 10

/-- `_PyUnicode_FormatLong(val, alt, prec, type)`, unicode_format.c:192-314. -/
def unicodeFormatLong (val : Int) (alt : Bool) (prec : Int) (type : Nat) : Py Seq := do
  if prec > intMax - 3 then throw (.overflowError "precision too large")
  let result ← numberToBase val (longBase type)
  if (result.length : Int) > intMax then
    throw (.valueError "string too large in _PyUnicode_FormatLong")
  return formatLongText result alt prec type

/-- `"%%%c requires %s, not %T"`, bytesobject.c:445 and :504. -/
def requiresMsg (type : Nat) (kind typeName : String) : String :=
  "%" ++ (Char.ofNat type).toString ++ " requires " ++ kind ++ ", not " ++ typeName

/-- `formatlong`, bytesobject.c:481-510. -/
def formatLong (st : FS) (v : Obj) (fl : Fl) (prec : Int) (type : Nat) : Py Seq :=
  let typeName := v.typeName
  let unsupported : PyExc :=
    let kind := if type = 111 ∨ type = 120 ∨ type = 88 then "an integer" else "a real number"
    formatError .typeError st (requiresMsg type kind typeName)
  match v.longValue? with
  | some i => unicodeFormatLong i fl.alt prec type
  | none =>
    if v.isNumber then
      -- make sure number is a type of integer for o, x, and X
      let iobj : Py Int :=
        if type = 111 ∨ type = 120 ∨ type = 88 then
          match v.index? with
          | some (.ok i) => .ok i
          | some (.error e) => .error e
          | none => .error (notInteger v)
        else numberLong v
      match iobj with
      | .ok i => unicodeFormatLong i fl.alt prec type
      | .error e => if isTypeError e then .error unsupported else .error e
    else .error unsupported

/-- `PyOS_double_to_string(x, type, prec, dtoa_flags, NULL)`, Python/pystrtod.c:1237-1308
(`Binary64.PyOS_double_to_string_checked`): the 3.15 `precision too big` guard, then the
text. A NULL from `_Py_dg_dtoa` is its `MemoryError`. -/
def doubleToString (x : Binary64.F64) (type : Nat) (prec : Int) (alt : Bool) : Py Seq :=
  match Binary64.PyOS_double_to_string_checked x type prec { alt } with
  | .error e => .error e
  | .ok none => .error memoryError
  | .ok (some (ps, _)) => .ok (Binary64.render ps)

/-- `formatfloat`, bytesobject.c:430-479, with the writer path (:461-470) and the
`PyBytes` path (:472-476) merged: both hand back the text of `PyOS_double_to_string`.
Only a `TypeError` of `PyFloat_AsDouble` is replaced (:441-448). -/
def formatFloatText (st : FS) (v : Obj) (fl : Fl) (prec : Int) (type : Nat) : Py Seq :=
  match asDouble v with
  | .error e =>
    if isTypeError e then
      .error (formatError .typeError st (requiresMsg type "a real number" v.typeName))
    else .error e
  | .ok x =>
    -- :451-456
    let prec := if prec < 0 then 6 else prec
    doubleToString x type prec fl.alt

/-- `byte_converter`, bytesobject.c:512-557. The last message is for an object with no `__index__`:
one whose `__index__` fails keeps its exception, :540-542. -/
def byteConverter (st : FS) (arg : Obj) : Py Nat :=
  match arg with
  | .bytes s =>
    if s.length ≠ 1 then
      .error (formatError .typeError st s!"%c requires an integer in range(256) or a single byte, not a bytes object of length {s.length}")
    else .ok (s.headD 0)
  | .bytearray s =>
    if s.length ≠ 1 then
      .error (formatError .typeError st s!"%c requires an integer in range(256) or a single byte, not a bytearray object of length {s.length}")
    else .ok (s.headD 0)
  | _ =>
    let bad : PyExc :=
      formatError .typeError st s!"%c requires an integer in range(256) or a single byte, not {arg.typeName}"
    match arg.index? with
    | some (.ok ival) =>
      -- this includes an overflow in converting to C long
      if !(0 ≤ ival ∧ ival ≤ 255) then
        .error (formatError .overflowError st "%c argument not in range(256)")
      else .ok ival.toNat
    | some (.error e) => .error e
    | none => .error bad

/-- `format_obj`, bytesobject.c:561-613. -/
def formatObj (st : FS) (v : Obj) : Py Seq :=
  match v with
  | .bytes s => .ok s
  | .bytearray s => .ok s
  | .dunderRaises e => .error e
  | .dunder r =>
    match r with
    | .bytes s => .ok s
    | _ => .error (bytesDunderWrong v r)
  | _ =>
    match v.buffer? with
    | some s => .ok s
    | none =>
      .error (formatError .typeError st
        s!"%b requires a bytes-like object, or an object that implements __bytes__, not {v.typeName}")

/-! ## The field writer -/

/-- What lines 1041-1054 of `_PyBytes_FormatEx` compute before writing:
`len`, `width`, `sign` after the sign block. -/
def signStep (isNum : Bool) (fl : Fl) (pbuf : Seq) (len : Int) : Nat × Seq × Int :=
  if isNum then
    match pbuf with
    | 45 :: rest => (45, rest, len - 1)
    | 43 :: rest => (43, rest, len - 1)
    | _ =>
      if fl.sign then (43, pbuf, len)
      else if fl.blank then (32, pbuf, len)
      else (0, pbuf, len)
  else (0, pbuf, len)

/-- `alloc`, bytesobject.c:1053-1058. -/
def fieldAlloc (sign : Nat) (width len : Int) : Int :=
  let width := if width < len then len else width
  if sign ≠ 0 ∧ len = width then width + 1 else width

/-- The prefix condition, bytesobject.c:1082 and :1107. -/
def hasPrefix (fl : Fl) (c : Int) : Bool := fl.alt && (c == 111 || c == 120 || c == 88)

/-- The writes of bytesobject.c:1071-1123 for the sign-processed field `pbuf`,
`len`: returns the bytes written. `width` is the value after line 971. -/
def fieldWrites (fl : Fl) (c : Int) (fill : Nat) (sign : Nat) (width len : Int) (pbuf : Seq) : Seq :=
  -- Write the sign if needed
  let o1 : Seq := if sign ≠ 0 ∧ fill ≠ 32 then [sign] else []
  let width := if sign ≠ 0 ∧ width > len then width - 1 else width
  -- Write the numeric prefix for "x", "X" and "o" formats if the alternate form is used
  let pre := hasPrefix fl c
  let o2 : Seq := if pre ∧ fill ≠ 32 then pbuf.take 2 else []
  let pbuf := if pre ∧ fill ≠ 32 then pbuf.drop 2 else pbuf
  let width := if pre then (if width - 2 < 0 then 0 else width - 2) else width
  let len := if pre then len - 2 else len
  -- Pad left with the fill character if needed
  let leftPad := width > len ∧ !fl.ljust
  let o3 : Seq := if leftPad then List.replicate (width - len).toNat fill else []
  let width := if leftPad then len else width
  -- If padding with spaces: write sign if needed and/or numeric prefix
  let o4 : Seq := if fill = 32 ∧ sign ≠ 0 then [sign] else []
  let o5 : Seq := if fill = 32 ∧ pre then pbuf.take 2 else []
  let pbuf := if fill = 32 ∧ pre then pbuf.drop 2 else pbuf
  -- Copy bytes
  let o6 := pbuf.take len.toNat
  -- Pad right with the fill character if needed
  let o7 : Seq := if width > len then List.replicate (width - len).toNat 32 else []
  o1 ++ o2 ++ o3 ++ o4 ++ o5 ++ o6 ++ o7

/-! ## The specifier parser -/

/-- `*fmt` as `c = *fmt++` stores it. -/
def readSigned (format : Seq) (st : FS) : Int := sgnChar (format.getD st.pos 0)

/-- The key loop, bytesobject.c:717-723. -/
def keyLoop (format : Seq) : Nat → FS → Nat → Py (FS × Nat)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, st, pcount =>
    if pcount > 0 then
      let cnt := st.cnt - 1
      if cnt ≥ 0 then
        let ch := format.getD st.pos 0
        let pcount := if ch = 41 then pcount - 1 else if ch = 40 then pcount + 1 else pcount
        keyLoop format fuel { st with cnt, pos := st.pos + 1 } pcount
      else .ok ({ st with cnt }, pcount)
    else .ok (st, pcount)

/-- `PyObject_GetItem(dict, key)` for the mappings the model has. -/
def mappingGet (d : Obj) (key : Seq) : Py Obj :=
  match d with
  | .dict kv =>
    match kv.find? (fun p => p.1 == key) with
    | some p => .ok p.2
    | none => .error (.keyError ("~" ++ String.ofList (key.map Char.ofNat)))
  | .list _ => .error (.typeError "list indices must be integers or slices, not bytes")
  | _ => .error (.typeError "~not subscriptable")

/-- Flag parsing, bytesobject.c:759-768. -/
def flagsLoop (format : Seq) : Nat → FS → Fl → Int → Py (FS × Fl × Int)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, st, fl, c =>
    let cnt := st.cnt - 1
    if cnt ≥ 0 then
      let c := readSigned format st
      let st := { st with cnt, pos := st.pos + 1 }
      if c = 45 then flagsLoop format fuel st { fl with ljust := true } c
      else if c = 43 then flagsLoop format fuel st { fl with sign := true } c
      else if c = 32 then flagsLoop format fuel st { fl with blank := true } c
      else if c = 35 then flagsLoop format fuel st { fl with alt := true } c
      else if c = 48 then flagsLoop format fuel st { fl with zero := true } c
      else .ok (st, fl, c)
    else .ok ({ st with cnt }, fl, c)

/-- A number after the first digit, bytesobject.c:807-818 and :857-868: `limit`
is `PY_SSIZE_T_MAX` or `INT_MAX`. -/
def digitsLoop (format : Seq) (limit : Int) (tooBig : String) :
    Nat → FS → Int → Int → Py (FS × Int × Int)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, st, n, c =>
    let cnt := st.cnt - 1
    if cnt ≥ 0 then
      let c : Int := format.getD st.pos 0  -- Py_CHARMASK
      let st := { st with cnt, pos := st.pos + 1 }
      if !(48 ≤ c ∧ c ≤ 57) then .ok (st, n, c)
      else if n > Int.tdiv (limit - (c - 48)) 10 then .error (.valueError tooBig)
      else digitsLoop format limit tooBig fuel st (n * 10 + (c - 48)) c
    else .ok ({ st with cnt }, n, c)

/-- `if (--fmtcnt >= 0) c = *fmt++;`, bytesobject.c:802-803 and :824-825, :852-853, :873-874. -/
def nextC (format : Seq) (st : FS) (c : Int) : FS × Int :=
  let cnt := st.cnt - 1
  if cnt ≥ 0 then ({ st with cnt, pos := st.pos + 1 }, readSigned format st)
  else ({ st with cnt }, c)

/-- The refusal of a `*` under a key, bytesobject.c:772-778 and :827-833. -/
def starKey (at' : Int) : PyExc :=
  .valueError s!"* cannot be used with a parenthesised mapping key at position {at'}"

/-- The `*` width, bytesobject.c:782-798: `PyLong_AsSsize_t`, and a width of `PY_SSIZE_T_MIN` has no
negation. -/
def starWidth (st : FS) (v : Obj) : Py Int :=
  match v.longValue? with
  | none => .error (formatError .typeError st s!"* requires int, not {v.typeName}")
  | some i =>
    if i ≤ ssizeMin ∨ i > ssizeMax then .error (formatError .overflowError st "too big for width")
    else .ok i

/-- The `*` precision, bytesobject.c:837-849: `PyLong_AsInt`. -/
def starPrec (st : FS) (v : Obj) : Py Int :=
  match v.longValue? with
  | none => .error (formatError .typeError st s!"* requires int, not {v.typeName}")
  | some i =>
    if i < -2147483648 ∨ i > 2147483647 then
      .error (formatError .overflowError st "too big for precision")
    else .ok i

/-- Width parsing, bytesobject.c:770-819. `at'` is `fmtstart - format - 1`. -/
def parseWidth (format : Seq) (at' : Int) (st : FS) (fl : Fl) (c : Int) :
    Py (FS × Fl × Int × Int) := do
  if c = 42 then
    if st.arglen < -1 then throw (starKey at')
    let (v, st) ← getNextArg st false
    let width ← starWidth st v
    let (fl, width) := if width < 0 then ({ fl with ljust := true }, -width) else (fl, width)
    let (st, c) := nextC format st c
    return (st, fl, width, c)
  else if 48 ≤ c ∧ c ≤ 57 then
    let (st, width, c) ← digitsLoop format ssizeMax s!"width too big at position {at'}"
      (format.length + 1) st (c - 48) c
    return (st, fl, width, c)
  else return (st, fl, -1, c)

/-- Precision parsing, bytesobject.c:821-870. -/
def parsePrec (format : Seq) (at' : Int) (st : FS) (c : Int) : Py (FS × Int × Int) := do
  if c = 46 then
    let (st, c) := nextC format st c
    if c = 42 then
      if st.arglen < -1 then throw (starKey at')
      let (v, st) ← getNextArg st false
      let prec ← starPrec st v
      let prec := if prec < 0 then 0 else prec
      let (st, c) := nextC format st c
      return (st, prec, c)
    else if 48 ≤ c ∧ c ≤ 57 then
      let (st, prec, c) ← digitsLoop format intMax s!"precision too big at position {at'}"
        (format.length + 1) st (c - 48) c
      return (st, prec, c)
    else return (st, 0, c)
  else return (st, -1, c)

/-- The text of the fast path `_PyLong_FormatBytesWriter(&writer, res, v, base,
alternate)`, Objects/longobject.c:2529-2547, and `long_to_decimal_string_internal`, :2096, or
`long_format_binary`, :2335: the sign, the base
marker for `alternate`, the digits. -/
def fastLong (v : Int) (c : Int) (alt : Bool) : Py Seq :=
  if c = 111 then
    .ok ((if v < 0 then [45] else []) ++ (if alt then asc "0o" else []) ++ digitsBase 8 v.natAbs)
  else if c = 120 then
    .ok ((if v < 0 then [45] else []) ++ (if alt then asc "0x" else []) ++ digitsBase 16 v.natAbs)
  else intRepr v

/-- Is `c` one of the integer conversions? bytesobject.c:918-923. -/
def isIntConv (c : Int) : Bool := c == 105 || c == 100 || c == 117 || c == 111 || c == 120 || c == 88

/-- Is `c` one of the float conversions? bytesobject.c:970-975. -/
def isFloatConv (c : Int) : Bool :=
  c == 101 || c == 69 || c == 102 || c == 70 || c == 103 || c == 71

/-- `Py_ISALPHA(c)` on a `c` read as a signed char: `_Py_ctype_table[Py_CHARMASK(c)]`. -/
def isAlphaFmt (c : Int) : Bool := (65 ≤ c ∧ c ≤ 90) ∨ (97 ≤ c ∧ c ≤ 122)

/-- The `default:` case, bytesobject.c:1007-1038: `at'` is `fmtstart - format - 1` and `pos` is
`fmt - format - 1`. -/
def unsupportedChar (c at' pos : Int) : PyExc :=
  let stray := s!"stray % at position {at'} or unexpected format character "
  if isAlphaFmt c then
    .valueError (s!"unsupported format %{Char.ofNat c.toNat} at position {at'}")
  else if c = 39 then .valueError (stray ++ s!"\"'\" at position {pos}")
  else if 32 ≤ c ∧ c < 127 then .valueError (stray ++ s!"'{Char.ofNat c.toNat}' at position {pos}")
  else
    .valueError (stray ++ "with code 0x" ++ seqText (hexN 2 (c % 256).toNat) ++ s!" at position {pos}")

/-- Lines 1041-1131 of `_PyBytes_FormatEx`: the sign block, the `alloc`
reservation, the writes and the mapping check. -/
def writeField (dict : Bool) (st : FS) (fl : Fl) (c : Int) (fill : Nat) (isNum : Bool)
    (width len : Int) (pbuf : Seq) : Py FS := do
  let (sign, pbuf, len) := signStep isNum fl pbuf len
  let width := if width < len then len else width
  let alloc := fieldAlloc sign width len
  -- 2: size preallocated for %s
  let w ← if alloc > 2 then writerGrow st.w (alloc - 2) else pure st.w
  let out := st.out ++ fieldWrites fl c fill sign width len pbuf
  if dict ∧ st.argidx < st.arglen then
    throw (.typeError "not all arguments converted during bytes formatting")
  return { st with w, out }

/-- One specifier, bytesobject.c:679-1138. On entry `st.pos` is at the `%` and
`--fmtcnt` has been done. -/
def formatSpec (format : Seq) (dict : Option Obj) (useBytearray : Bool) (st : FS) : Py FS := do
  let st := { st with pos := st.pos + 1 }
  if format.getD st.pos 0 = 37 then
    return { st with out := st.out ++ [37], pos := st.pos + 1, cnt := st.cnt - 1 }
  let st := { st with key := none }
  let at' : Int := (st.pos : Int) - 1
  let st ← do
    if format.getD st.pos 0 = 40 then
      match dict with
      | none => throw (.typeError s!"format requires a mapping, not {st.args.typeName}")
      | some d =>
        let st := { st with pos := st.pos + 1, cnt := st.cnt - 1 }
        let keystart := st.pos
        -- Skip over balanced parentheses
        let (st, pcount) ← keyLoop format (format.length + 2) st 1
        if st.cnt < 0 ∨ pcount > 0 then
          throw (.valueError s!"stray % or incomplete format key at position {at'}")
        let key := (format.drop keystart).take (st.pos - keystart - 1)
        let args ← mappingGet d key
        pure { st with args, arglen := -3, argidx := -4, key := some key }
    else if st.arglen < -1 then
      throw (.valueError s!"format requires a parenthesised mapping key at position {at'}")
    else pure st
  -- Parse flags. Example: "%+i" => flags=F_SIGN.
  let (st, fl, c) ← flagsLoop format (format.length + 2) st {} 0
  -- Parse width. Example: "%10s" => width=10
  let (st, fl, width, c) ← parseWidth format at' st fl c
  -- Parse precision. Example: "%.3f" => prec=3
  let (st, prec, c) ← parsePrec format at' st c
  let (st, c) :=
    if st.cnt ≥ 0 ∧ (c = 104 ∨ c = 108 ∨ c = 76) then nextC format st c else (st, c)
  if st.cnt < 0 then throw (.valueError s!"stray % at position {at'}")
  let (v, st) ← getNextArg st true
  -- last write: disable writer overallocation
  let st := if st.cnt = 0 then { st with w := { st.w with overallocate := false } } else st
  let isDict := dict.isSome
  if c = 114 ∨ c = 97 then
    -- %a, and %r "only for 2/3 code"
    let temp ← asciiObj 8 v
    let len : Int := temp.length
    let len := if prec ≥ 0 ∧ len > prec then prec else len
    writeField isDict st fl c 32 false width len temp
  else if c = 115 ∨ c = 98 then
    -- %b, and %s "only for 2/3 code"
    let temp ← formatObj st v
    let len : Int := temp.length
    let len := if prec ≥ 0 ∧ len > prec then prec else len
    writeField isDict st fl c 32 false width len temp
  else if isIntConv c then
    let isExact : Bool := match v with | .int _ => true | _ => false
    if isExact = true ∧ width = -1 ∧ prec = -1 ∧ !(fl.sign ∨ fl.blank) ∧ c ≠ 88 then
      -- Fast path
      let i := match v with | .int i => i | _ => 0
      let text ← fastLong i c fl.alt
      let w ← writerGrow st.w text.length
      return { st with w, out := st.out ++ text }
    else
      let temp ← formatLong st v fl prec c.toNat
      writeField isDict st fl c (if fl.zero then 48 else 32) true width temp.length temp
  else if isFloatConv c then
    if width = -1 ∧ prec = -1 ∧ !(fl.sign ∨ fl.blank) then
      -- Fast path
      let text ← formatFloatText st v fl prec c.toNat
      let w ← writerGrow st.w text.length
      return { st with w, out := st.out ++ text }
    else
      let temp ← formatFloatText st v fl prec c.toNat
      writeField isDict st fl c (if fl.zero then 48 else 32) true width temp.length temp
  else if c = 99 then
    let onechar ← byteConverter st v
    if width = -1 then
      -- Fast path
      return { st with out := st.out ++ [onechar] }
    else writeField isDict st fl c 32 false width 1 [onechar]
  else
    throw (unsupportedChar c at' ((st.pos : Int) - 1))

/-- `_PyBytes_FormatEx`'s main loop, bytesobject.c:661-1143. A literal run,
lines 662-677; a specifier otherwise. Every iteration consumes at least one byte. -/
def formatLoop (format : Seq) (dict : Option Obj) (useBytearray : Bool) : Nat → FS → Py FS
  | 0, _ => .error .modelFuel
  | fuel + 1, st =>
    let cnt := st.cnt - 1
    if cnt ≥ 0 then
      let st := { st with cnt }
      if format.getD st.pos 0 ≠ 37 then
        let rest := (format.drop (st.pos + 1)).take cnt.toNat
        let len : Int :=
          match rest.findIdx? (· == 37) with
          | some i => (i : Int) + 1
          | none => cnt + 1
        let out := st.out ++ (format.drop st.pos).take len.toNat
        formatLoop format dict useBytearray fuel
          { st with out, pos := st.pos + len.toNat, cnt := cnt - (len - 1) }
      else
        match formatSpec format dict useBytearray st with
        | .ok st => formatLoop format dict useBytearray fuel st
        | .error e => .error e
    else .ok { st with cnt }

/-- The mapping test of `_PyBytes_FormatEx`, bytesobject.c:655-659. -/
def asMapping (args : Obj) : Option Obj :=
  match args with
  | .dict _ | .list _ | .memview _ _ => some args
  | _ => none

/-- `_PyBytes_FormatEx(format, format_len, args, use_bytearray)`, bytesobject.c:617-1167. -/
def bytesFormatEx (format : Seq) (args : Obj) (useBytearray : Bool) : Py Seq := do
  let w ← writerCreate format.length useBytearray
  let (arglen, argidx) : Int × Int :=
    match args with
    | .tuple xs => (xs.length, 0)
    | _ => (-1, -2)
  let dict := asMapping args
  let st ← formatLoop format dict useBytearray (format.length + 1)
    { pos := 0, cnt := format.length, out := [], w, args, arglen, argidx }
  if st.argidx < st.arglen ∧ dict.isNone then
    throw (.typeError (s!"not all arguments converted during bytes formatting " ++
      s!"(required {if st.arglen < 0 then 0 else st.argidx}, got {if st.arglen < 0 then 1 else st.arglen})"))
  writerFinish st.w st.out

/-- `bytes_mod(self, arg)`, bytesobject.c:2842-2850. `none` is `NotImplemented`, the answer
when `self` fails `PyBytes_Check` (:2845-2847): the `nb_remainder` slot is also called for
`x % b` with the bytes on the right, as `bytes.__rmod__` does. -/
def bytesModObj (self arg : Obj) : Py (Option Seq) :=
  match self with
  | .bytes s => some <$> bytesFormatEx s arg false
  | _ => .ok none

/-- `bytes_mod` on a bytes `self`. -/
def bytesMod (format : Seq) (args : Obj) : Py Seq := bytesFormatEx format args false

/-- `bytearray_mod`, bytearrayobject.c:2913-2945. -/
def bytearrayMod (format : Seq) (args : Obj) : Py Seq := bytesFormatEx format args true

end PyLean.BytesObj.Bytes
