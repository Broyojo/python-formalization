import PyLean.UnicodeObj.FormatNumber
import PyLean.UnicodeObj.Repr
import PyLean.Binary64.Float

/-!
`%`-formatting, `PyUnicode_Format` and its helpers, Objects/unicode_format.c:97-1114.

Arguments are a small universe of objects: `int`, `bool`, `float`, `str`, `None`, and a `dict` used
as one argument. Generic objects would go through their `__str__`, `__repr__` and `__index__`; those
cases are not modelled.
-/

namespace PyLean.UnicodeObj

open PyLean PyLean.Binary64

/-- The objects `%` is modelled on. -/
inductive FObj where
  | int (v : Int)
  | bool (b : Bool)
  | float (x : F64)
  | str (s : Str)
  | none
  /-- A `dict` taken as one argument, by what its `repr` gives, which is an exception for an `int`
  over the digit limit. `repr` runs only if a conversion asks for it. -/
  | mapping (shown : Str) (fails : Option PyExc)
  deriving Repr, DecidableEq

def FObj.typeName : FObj → String
  | .int _ => "int"
  | .bool _ => "bool"
  | .float _ => "float"
  | .str _ => "str"
  | .none => "NoneType"
  | .mapping _ _ => "dict"

/-- `args`: a tuple, a dict, or one other object. -/
inductive FArgs where
  | tuple (items : List FObj)
  | dict (items : List (Str × FObj))
  | single (o : FObj)
  deriving Repr, DecidableEq

/-- `%T` of `ctx->args`. -/
def FArgs.typeName : FArgs → String
  | .tuple _ => "tuple"
  | .dict _ => "dict"
  | .single o => o.typeName

/-- `F_LJUST`, `F_SIGN`, `F_BLANK`, `F_ALT`, `F_ZERO`. -/
structure FFlags where
  ljust : Bool := false
  sign : Bool := false
  blank : Bool := false
  alt : Bool := false
  zero : Bool := false
  deriving Repr, DecidableEq

/-- `struct unicode_format_arg_t`. -/
structure FArg where
  ch : Nat
  flags : FFlags := {}
  width : Int := -1
  prec : Int := -1
  sign : Bool := false
  fmtstart : Nat := 0
  key : Option Str := none
  deriving Repr, DecidableEq

/-- The mutable part of `struct unicode_formatter_t`. `cur` is `ctx->args`. -/
structure FCtx where
  cur : FArgs
  arglen : Int
  argidx : Int
  dict : Option (List (Str × FObj))
  deriving Repr, DecidableEq

/-- The element `ctx->args` holds when it is not a tuple. -/
def FArgs.obj : FArgs → FObj
  | .single o => o
  | _ => .none

/-- `str(key)` as `KeyError` prints it, and `%R` of a key. -/
def keyErrorText (key : Str) : String := toLeanString (unicodeRepr key)

/-- `FORMAT_ERROR`, unicode_format.c:81-93. `ctx.argidx` has moved past the argument. -/
def formatErr (mk : String → PyExc) (ctx : FCtx) (arg : FArg) (msg : String) : PyExc :=
  match arg.key with
  | some k => mk s!"format argument {keyErrorText k}: {msg}"
  | none =>
    if ctx.argidx ≥ 0 then mk s!"format argument {ctx.argidx}: {msg}"
    else mk s!"format argument: {msg}"

/-- `unicode_format_getnextarg`, unicode_format.c:97-114. With `allowone` false a `*` cannot take a
lone argument. -/
def getNextArg (allowone : Bool) (ctx : FCtx) : Py (FObj × FCtx) :=
  if ctx.argidx < ctx.arglen ∧ (allowone = true ∨ ctx.arglen ≥ 0) then
    let ctx' := { ctx with argidx := ctx.argidx + 1 }
    if ctx.arglen < 0 then .ok (ctx.cur.obj, ctx')
    else
      match ctx.cur with
      | .tuple items => .ok (items.getD ctx.argidx.toNat .none, ctx')
      | _ => .ok (.none, ctx')
  else
    .error (.typeError
      s!"not enough arguments for format string (got {if ctx.arglen < 0 then 1 else ctx.arglen})")

/-- The state of the argument parser: `arg`, the unread format, `fmtcnt < 0`. -/
structure FParse where
  arg : FArg
  rest : List Nat
  exhausted : Bool
  ctx : FCtx
  deriving Repr, DecidableEq

/-- `if (--ctx->fmtcnt >= 0) { arg->ch = FORMAT_READ(ctx); ctx->fmtpos++; }`. -/
def FParse.next (p : FParse) : FParse :=
  match p.rest with
  | [] => { p with exhausted := true }
  | c :: t => { p with arg := { p.arg with ch := c }, rest := t }

/-- The flag loop, unicode_format.c:529-540. -/
def parseFlagsLoop : Nat → FParse → FParse
  | 0, p => p
  | fuel + 1, p =>
    let p := p.next
    if p.exhausted then p
    else
      let a := p.arg
      let fl := a.flags
      let setF (g : FFlags) : FParse := { p with arg := { a with flags := g } }
      if a.ch == 45 then parseFlagsLoop fuel (setF { fl with ljust := true })
      else if a.ch == 43 then parseFlagsLoop fuel (setF { fl with sign := true })
      else if a.ch == 32 then parseFlagsLoop fuel (setF { fl with blank := true })
      else if a.ch == 35 then parseFlagsLoop fuel (setF { fl with alt := true })
      else if a.ch == 48 then parseFlagsLoop fuel (setF { fl with zero := true })
      else p

def isAsciiDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

/-- The digit loops of the width and precision: `limit` is `PY_SSIZE_T_MAX` or `INT_MAX`. -/
def digitsLoop (limit : Int) (msg : String) : Nat → Int → FParse → Py (Int × FParse)
  | 0, v, p => .ok (v, p)
  | fuel + 1, v, p =>
    let p := p.next
    if p.exhausted then .ok (v, p)
    else
      let c := p.arg.ch
      if !isAsciiDigit c then .ok (v, p)
      else
        let d : Int := (c : Int) - 48
        if v > (limit - d) / 10 then .error (.valueError msg)
        else digitsLoop limit msg fuel (v * 10 + d) p

/-- An `int` or `bool` as `PyLong_Check` sees it. -/
def FObj.asLong : FObj → Option Int
  | .int v => some v
  | .bool b => some (if b then 1 else 0)
  | _ => Option.none

/-- The refusal of a `*` in a `%(key)` conversion. -/
def starKeyError (start : Nat) : PyExc :=
  .valueError s!"* cannot be used with a parenthesised mapping key at position {start}"

/-- The `*` and digit width, unicode_format.c:543-597. `PyLong_AsSsize_t` overflows, and
`PY_SSIZE_T_MIN`, which has no negation, gets the same error. -/
def parseWidthArg (fuel : Nat) (p : FParse) : Py FParse := do
  if p.arg.ch == 42 then
    if p.ctx.arglen < -1 then .error (starKeyError p.arg.fmtstart) else
    let (v, ctx) ← getNextArg false p.ctx
    let some l := v.asLong |
      .error (formatErr .typeError ctx p.arg s!"* requires int, not {v.typeName}")
    let big := formatErr .overflowError ctx p.arg "too big for width"
    if l < ssizeMin ∨ l > ssizeMax then .error big else
    if l = ssizeMin then .error big else
    let (w, flags) := if l < 0 then (-l, { p.arg.flags with ljust := true })
      else (l, p.arg.flags)
    .ok ({ p with arg := { p.arg with width := w, flags := flags }, ctx := ctx } : FParse).next
  else if isAsciiDigit p.arg.ch then
    let (w, p') ← digitsLoop ssizeMax s!"width too big at position {p.arg.fmtstart}" fuel
      ((p.arg.ch : Int) - 48) p
    .ok { p' with arg := { p'.arg with width := w } }
  else .ok p

/-- The precision, unicode_format.c:600-652. -/
def parsePrecArg (fuel : Nat) (p : FParse) : Py FParse := do
  if p.arg.ch != 46 then .ok p
  else
    let p := ({ p with arg := { p.arg with prec := 0 } } : FParse).next
    if p.arg.ch == 42 then
      if p.ctx.arglen < -1 then .error (starKeyError p.arg.fmtstart) else
      let (v, ctx) ← getNextArg false p.ctx
      let some l := v.asLong |
        .error (formatErr .typeError ctx p.arg s!"* requires int, not {v.typeName}")
      if l < -(2 ^ 31) ∨ l > 2 ^ 31 - 1 then
        .error (formatErr .overflowError ctx p.arg "too big for precision") else
      .ok ({ p with arg := { p.arg with prec := if l < 0 then 0 else l }, ctx := ctx } : FParse).next
    else if isAsciiDigit p.arg.ch then
      let (v, p') ← digitsLoop (2 ^ 31 - 1) s!"precision too big at position {p.arg.fmtstart}" fuel
        ((p.arg.ch : Int) - 48) p
      .ok { p' with arg := { p'.arg with prec := v } }
    else .ok p

/-- The key of `%(key)`, unicode_format.c:487-495: the key and what follows, or `none` for an
incomplete key. -/
def scanKey : Nat → Nat → List Nat → List Nat → Option (List Nat × List Nat)
  | _, _, _, [] => none
  | 0, _, _, _ => none
  | fuel + 1, pcount, key, c :: t =>
    let pcount' := if c == 41 then pcount - 1 else if c == 40 then pcount + 1 else pcount
    if pcount' = 0 then some (key.reverse, t)
    else scanKey fuel pcount' (c :: key) t

/-- `unicode_format_arg_parse`, unicode_format.c:464-671. On entry `p.rest` starts at the character
after `%`, which the flag loop reads again (`fmtpos` has not moved), and `p.arg.ch` already holds
it. -/
def formatArgParse (p : FParse) : Py FParse := do
  let fuel := p.rest.length + 1
  let start := p.arg.fmtstart
  let p ←
    if p.arg.ch == 40 then
      match p.ctx.dict with
      | none => .error (.typeError s!"format requires a mapping, not {p.ctx.cur.typeName}")
      | some items =>
        match scanKey fuel 1 [] p.rest.tail with
        | none => .error (.valueError s!"stray % or incomplete format key at position {start}")
        | some (key, rest) =>
          match items.lookup key with
          | none => .error (.keyError (keyErrorText key))
          | some v =>
            .ok ({ p with rest := rest, arg := { p.arg with key := some key },
                          ctx := { p.ctx with cur := .single v, arglen := -3, argidx := -4 } } :
                  FParse)
    else if p.ctx.arglen < -1 then
      .error (.valueError s!"format requires a parenthesised mapping key at position {start}")
    else pure p
  let p := parseFlagsLoop fuel p
  let p ← parseWidthArg fuel p
  let p ← parsePrecArg fuel p
  let p : FParse :=
    if !p.exhausted && (p.arg.ch == 104 || p.arg.ch == 108 || p.arg.ch == 76) then p.next else p
  if p.exhausted then .error (.valueError s!"stray % at position {start}") else .ok p

/-- `_PyUnicode_FormatLong`, unicode_format.c:193-315. -/
def formatLongStr (v : Int) (alt : Bool) (prec : Int) (type : Nat) : Py Str := do
  if prec > 2 ^ 31 - 1 - 3 then .error (.overflowError "precision too large")
  else
    let base : Nat := if type == 111 then 8 else if type == 120 || type == 88 then 16 else 10
    let result ← longFormat v base
    let nonDigitsBase : Nat := if base == 10 then 0 else 2
    let sign := result.head? == some 45
    let numnondigits := nonDigitsBase + (if sign then 1 else 0)
    let numdigits := result.length - numnondigits
    -- `alt == 0`: drop the prefix, keeping the sign
    let (buf, numnondigits) :=
      if !alt && base != 10 then
        ((if sign then [45] else []) ++ result.drop numnondigits, numnondigits - 2)
      else (result, numnondigits)
    let buf :=
      if prec > numdigits then
        buf.take numnondigits ++ List.replicate (prec.toNat - numdigits) 48 ++ buf.drop numnondigits
      else buf
    .ok (if type == 88 then
      buf.map fun c => if 97 ≤ c ∧ c ≤ 120 then c - 32 else c else buf)

/-- `str(v)`. -/
def FObj.strOf : FObj → Py Str
  | .int v => longFormat v 10 false
  | .bool b => .ok (lit (if b then "True" else "False"))
  | .float x =>
    match float_repr x with
    | Option.none => .error .modelFuel
    | some s => .ok s
  | .str s => .ok s
  | .none => .ok (lit "None")
  | .mapping s Option.none => .ok s
  | .mapping _ (Option.some e) => .error e

/-- `repr(v)`. -/
def FObj.reprOf : FObj → Py Str
  | .str s => .ok (unicodeRepr s)
  | o => o.strOf

/-- `backslashreplace` on the non-ASCII characters, unicodeobject.c:763-825. -/
def asciiEscapeChar (c : Nat) : Str :=
  if c < 128 then [c]
  else if c < 0x100 then [92, 120] ++ hexDigits 2 c
  else if c < 0x10000 then [92, 117] ++ hexDigits 4 c
  else [92, 85] ++ hexDigits 8 c

/-- `ascii(v)`: `PyObject_ASCII`, Objects/object.c. -/
def FObj.asciiOf (o : FObj) : Py Str := do
  return (← o.reprOf).flatMap asciiEscapeChar

/-- What `unicode_format_arg_format` produced. -/
inductive FOut where
  /-- Written to the writer (return value 1). -/
  | direct (s : Str)
  /-- In `*p_str`, for `unicode_format_arg_output` (return value 0). -/
  | viaOutput (s : Str) (sign : Bool)
  deriving Repr, DecidableEq

/-- `mainformatlong`, unicode_format.c:323-413. -/
def mainFormatLong (ctx : FCtx) (v : FObj) (arg : FArg) : Py FOut := do
  let t := arg.ch
  let wrong : PyExc :=
    if t == 111 || t == 120 || t == 88 then
      formatErr .typeError ctx arg s!"%{Char.ofNat t} requires an integer, not {v.typeName}"
    else
      formatErr .typeError ctx arg s!"%{Char.ofNat t} requires a real number, not {v.typeName}"
  let iobj ← match v with
    | .float x =>
      -- `_PyNumber_Index` fails with a TypeError; `PyNumber_Long` keeps its own errors
      if t == 111 || t == 120 || t == 88 then .error wrong else PyLong_FromDouble x
    | _ =>
      match v.asLong with
      | some i => .ok i
      | Option.none => .error wrong
  let exact := match v with | .int _ => true | _ => false
  if exact && arg.width == -1 && arg.prec == -1 && !arg.flags.sign && !arg.flags.blank &&
      t != 88 then
    let base : Nat := if t == 111 then 8 else if t == 120 then 16 else 10
    return .direct (← longFormat iobj base arg.flags.alt)
  else
    return .viaOutput (← formatLongStr iobj arg.flags.alt arg.prec t) true

/-- `formatchar`, unicode_format.c:417-454. -/
def formatChar (ctx : FCtx) (arg : FArg) : FObj → Py Nat
  | .str s =>
    match s with
    | [c] => .ok c
    | _ => .error (formatErr .typeError ctx arg
        s!"%c requires an integer or a unicode character, not a string of length {s.length}")
  | .none => .error (formatErr .typeError ctx arg
      "%c requires an integer or a unicode character, not NoneType")
  | .float _ => .error (formatErr .typeError ctx arg
      "%c requires an integer or a unicode character, not float")
  | .mapping _ _ => .error (formatErr .typeError ctx arg
      "%c requires an integer or a unicode character, not dict")
  | o =>
    let x := (o.asLong).getD 0
    if x < 0 ∨ x > maxUnicode then
      .error (formatErr .overflowError ctx arg "%c argument not in range(0x110000)")
    else .ok x.toNat

/-- `PyFloat_AsDouble` on the objects of the universe. -/
def FObj.asDouble : FObj → Py F64
  | .float x => .ok x
  | .int v =>
    if v.natAbs ≥ 2 ^ 1024 - 2 ^ 970 then .error (.overflowError "int too large to convert to float")
    else .ok (F64.ofInt v)
  | .bool b => .ok (F64.ofInt (if b then 1 else 0))
  | v => .error (.typeError s!"must be real number, not {v.typeName}")

/-- `formatfloat`, unicode_format.c:124-171: a `TypeError` is replaced, an `OverflowError` is not. -/
def formatFloatPct (ctx : FCtx) (v : FObj) (arg : FArg) : Py Str := do
  let x ← match v.asDouble with
    | .error (.typeError _) => .error (formatErr .typeError ctx arg
        s!"%{Char.ofNat arg.ch} requires a real number, not {v.typeName}")
    | r => r
  let prec : Int := if arg.prec < 0 then 6 else arg.prec
  doubleToString x arg.ch prec { alt := arg.flags.alt }

/-- `%04X`. -/
def hex04X (c : Nat) : String :=
  let d := (Nat.toDigits 16 c).map Char.toUpper
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- `Py_ISALPHA` for a character under 128. -/
def isAsciiAlpha (c : Nat) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)

/-- The `default:` of `unicode_format_arg_format`, unicode_format.c:777-810. `index` is `fmtpos - 1`,
and `start` is `arg->fmtstart`. -/
def unsupportedFormat (c start index : Nat) : PyExc :=
  let stray := s!"stray % at position {start} or unexpected format character"
  if c < 128 ∧ isAsciiAlpha c then
    .valueError s!"unsupported format %{Char.ofNat c} at position {start}"
  else if c == 39 then .valueError s!"{stray} \"'\" at position {index}"
  else if 32 ≤ c ∧ c < 127 then .valueError s!"{stray} '{Char.ofNat c}' at position {index}"
  else if isPrintable c then
    .valueError s!"{stray} '{Char.ofNat c}' (U+{hex04X c}) at position {index}"
  else .valueError s!"{stray} U+{hex04X c} at position {index}"

/-- `unicode_format_arg_format`, unicode_format.c:689-816. `index` is `fmtpos - 1`. -/
def formatArgFormat (ctx : FCtx) (arg : FArg) (index : Nat) : Py (FOut × FCtx) := do
  let (v, ctx) ← getNextArg true ctx
  let c := arg.ch
  if c == 115 || c == 114 || c == 97 then
    match v with
    | .int n =>
      if arg.width == -1 && arg.prec == -1 then
        return (.direct (← longFormat n 10 false), ctx)
      else pure ()
    | _ => pure ()
    let s ← if c == 115 then v.strOf else if c == 114 then v.reprOf else v.asciiOf
    return (.viaOutput s false, ctx)
  else if c == 105 || c == 100 || c == 117 || c == 111 || c == 120 || c == 88 then
    return (← mainFormatLong ctx v arg, ctx)
  else if c == 101 || c == 69 || c == 102 || c == 70 || c == 103 || c == 71 then
    let s ← formatFloatPct ctx v arg
    if arg.width == -1 && arg.prec == -1 && !arg.flags.sign && !arg.flags.blank then
      return (.direct s, ctx)
    else return (.viaOutput s true, ctx)
  else if c == 99 then
    let ch ← formatChar ctx arg v
    if arg.width == -1 && arg.prec == -1 then return (.direct [ch], ctx)
    else return (.viaOutput [ch] false, ctx)
  else .error (unsupportedFormat c arg.fmtstart index)

/-- The part of `unicode_format_arg_output` after the sign is known, unicode_format.c:880-969:
`sign`, `signchar`, `len`, `pindex` on entry. -/
def formatArgTail (arg : FArg) (fill : Nat) (sign : Bool) (signchar : Nat) (len : Int) (pindex : Nat)
    (str : Str) : Str :=
  let fl := arg.flags
  let width : Int := if arg.width < len then len else arg.width
  let hasAlt := fl.alt && (arg.ch == 120 || arg.ch == 88 || arg.ch == 111)
  let out1 : Str := if sign && fill != 32 then [signchar] else []
  let width := if sign && width > len then width - 1 else width
  let out2 : Str := if hasAlt && fill != 32 then [48, arg.ch] else []
  let width := if hasAlt then max 0 (width - 2) else width
  let lenAfter : Int := if hasAlt then len - 2 else len
  let pindex := if hasAlt then pindex + 2 else pindex
  let pad : Nat := if width > lenAfter && !fl.ljust then (width - lenAfter).toNat else 0
  let width := if width > lenAfter && !fl.ljust then lenAfter else width
  let out3 : Str := if fill == 32 && sign then [signchar] else []
  let out4 : Str := if fill == 32 && hasAlt then [48, arg.ch] else []
  let body := (str.drop pindex).take lenAfter.toNat
  let tail : Nat := if width > lenAfter then (width - lenAfter).toNat else 0
  out1 ++ out2 ++ List.replicate pad fill ++ out3 ++ out4 ++ body ++ List.replicate tail 32

/-- `unicode_format_arg_output`, unicode_format.c:820-969, with `sign0` for `arg->sign`. -/
def formatArgOutput (arg : FArg) (sign0 : Bool) (str : Str) : Str :=
  let fl := arg.flags
  let fill : Nat := if sign0 && fl.zero then 48 else 32
  let len0 : Int := str.length
  if (arg.width == -1 ∨ arg.width ≤ len0) ∧ (arg.prec == -1 ∨ arg.prec ≥ len0) ∧
      !fl.sign ∧ !fl.blank then str
  else
    let strType := arg.ch == 115 || arg.ch == 114 || arg.ch == 97
    let len : Int := if strType ∧ arg.prec ≥ 0 ∧ len0 > arg.prec then arg.prec else len0
    let c0 := str.headD 0
    -- the sign
    let (sign, signchar, len, pindex) : Bool × Nat × Int × Nat :=
      if sign0 then
        if c0 == 45 || c0 == 43 then (true, c0, len - 1, 1)
        else if fl.sign then (true, 43, len, 0)
        else if fl.blank then (true, 32, len, 0)
        else (false, 0, len, 0)
      else (false, 0, len, 0)
    formatArgTail arg fill sign signchar len pindex str

/-- The final check of `unicode_format_arg`. -/
def checkDictArgs (ctx : FCtx) : Py Unit :=
  if ctx.dict.isSome && ctx.argidx < ctx.arglen then
    .error (.typeError "not all arguments converted during string formatting")
  else .ok ()

/-- `unicode_format_arg`, unicode_format.c:975-1027: output, what follows, context. -/
def formatArg (fmtlen : Nat) (rest : List Nat) (ctx : FCtx) : Py (Str × List Nat × FCtx) := do
  let ch := rest.headD 0
  if ch == 37 then return ([37], rest.tail, ctx)
  let p0 : FParse := { arg := { ch := ch, fmtstart := fmtlen - rest.length - 1 }, rest := rest,
                       exhausted := false, ctx := ctx }
  let p ← formatArgParse p0
  let (r, ctx') ← formatArgFormat p.ctx p.arg (fmtlen - p.rest.length - 1)
  let out := match r with
    | .direct s => s
    | .viaOutput s sign => formatArgOutput p.arg sign s
  checkDictArgs ctx'
  return (out, p.rest, ctx')

/-- The main loop of `PyUnicode_Format`. -/
def formatLoop (fmtlen : Nat) : Nat → List Nat → FCtx → Str → Py (Str × FCtx)
  | 0, _, _, _ => .error .modelFuel
  | _ + 1, [], ctx, out => .ok (out, ctx)
  | fuel + 1, c :: t, ctx, out => do
    if c != 37 then formatLoop fmtlen fuel t ctx (out ++ [c])
    else
      let (o, rest, ctx') ← formatArg fmtlen t ctx
      formatLoop fmtlen fuel rest ctx' (out ++ o)

/-- The message at unicode_format.c:1095-1099. -/
def notConvertedMsg (required got : Int) : String :=
  s!"not all arguments converted during string formatting (required {required}, got {got})"

/-- `repr` of a `dict` of the universe. -/
def dictRepr (items : List (Str × FObj)) : Py Str := do
  let parts ← items.mapM fun kv => do
    return unicodeRepr kv.1 ++ lit ": " ++ (← kv.2.reprOf)
  .ok (lit "{" ++ (lit ", ").intercalate parts ++ lit "}")

/-- `PyUnicode_Format`, unicode_format.c:1031-1114. A `dict` is also `ctx->args`, the one argument
of a conversion with no key. -/
def pyUnicodeFormat (format : Str) (args : FArgs) : Py Str := do
  let ctx : FCtx ← match args with
    | .tuple items => .ok { cur := args, arglen := items.length, argidx := 0, dict := none }
    | .dict items =>
      let shown := match dictRepr items with
        | .ok s => FObj.mapping s Option.none
        | .error e => FObj.mapping [] (Option.some e)
      .ok { cur := .single shown, arglen := -1, argidx := -2, dict := some items }
    | .single _ => .ok { cur := args, arglen := -1, argidx := -2, dict := none }
  let (out, ctx) ← formatLoop format.length (format.length + 1) format ctx []
  if ctx.argidx < ctx.arglen && ctx.dict.isNone then
    .error (.typeError (notConvertedMsg (if ctx.arglen < 0 then 0 else ctx.argidx)
      (if ctx.arglen < 0 then 1 else ctx.arglen)))
  else .ok out

/-- A `*` width that `getNextArg` gets as an `int`. In 3.14.7 `PY_SSIZE_T_MIN` was negated, which is
undefined in C; now it raises. So no negative width reaches the output step, the minimum is refused
like a width too big for `Py_ssize_t`, and every other width comes out as its size with `-` set if
it was negative. -/
def StarWidthSpec : Prop :=
  ∀ (fuel : Nat) (p : FParse) (v : Int) (ctx' : FCtx), p.arg.ch = 42 → p.ctx.arglen ≥ -1 →
    getNextArg false p.ctx = .ok (.int v, ctx') →
    match parseWidthArg fuel p with
    | .ok q =>
      ssizeMin < v ∧ v ≤ ssizeMax ∧ q.arg.width = (v.natAbs : Int) ∧
        q.arg.flags.ljust = (p.arg.flags.ljust || decide (v < 0))
    | .error e =>
      (v ≤ ssizeMin ∨ v > ssizeMax) ∧ e = formatErr .overflowError ctx' p.arg "too big for width"

theorem starWidthSpec_proven : StarWidthSpec := by
  intro fuel p v ctx' h42 hlen hget
  have hb : (p.arg.ch == 42) = true := by simp [h42]
  have hn : ¬p.ctx.arglen < -1 := by omega
  by_cases h1 : v < ssizeMin ∨ v > ssizeMax
  · simp only [parseWidthArg, hb, if_true, if_neg hn, bind, Except.bind, hget, FObj.asLong, if_pos h1]
    refine ⟨?_, trivial⟩
    rcases h1 with h | h
    · exact .inl (by omega)
    · exact .inr h
  by_cases h2 : v = ssizeMin
  · simp only [parseWidthArg, hb, if_true, if_neg hn, bind, Except.bind, hget, FObj.asLong, if_neg h1,
      if_pos h2]
    exact ⟨.inl (by omega), trivial⟩
  simp only [parseWidthArg, hb, if_true, if_neg hn, bind, Except.bind, hget, FObj.asLong, if_neg h1,
    if_neg h2]
  have hv : ssizeMin < v ∧ v ≤ ssizeMax := by omega
  by_cases h3 : v < 0
  · simp only [if_pos h3, FParse.next]
    split <;> exact ⟨hv.1, hv.2, by simp; omega, by simp [h3]⟩
  · simp only [if_neg h3, FParse.next]
    split <;> exact ⟨hv.1, hv.2, by simp; omega, by simp [h3]⟩

/-- `formatLongStr` with no precision is what the fast path `_PyLong_FormatWriter`
writes, for `%d`, `%o`, `%x`, with or without `#`, for every int. -/
def PercentIntFastSlow : Prop :=
  ∀ (v : Int) (alt : Bool) (t base : Nat),
    ((t = 100 ∧ base = 10) ∨ (t = 111 ∧ base = 8) ∨ (t = 120 ∧ base = 16)) →
    formatLongStr v alt (-1) t = longFormat v base alt

example : pyUnicodeFormat (lit "%d") (.tuple [.int 7]) = .ok (lit "7") := by decide +kernel
example : pyUnicodeFormat (lit "%5s|") (.tuple [.str (lit "a")]) = .ok (lit "    a|") := by
  decide +kernel

end PyLean.UnicodeObj
