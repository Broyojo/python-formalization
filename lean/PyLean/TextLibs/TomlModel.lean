import PyLean.UnicodeObj.CodecUtf8
import PyLean.UnicodeObj.Repr

/-!
Model of `Lib/tomllib/_parser.py` and `Lib/tomllib/_re.py`, CPython 3.15.2 (TOML 1.1.0).

A `str` is a list of code points and a position an index into it. `src[pos]` inside
`try: ... except IndexError` is `src[pos]?`; positions are never negative.

The values the parser builds are `TVal`s: a dict is an association list in insertion order
(`dict` keeps it), a list is a list. The parser mutates nested dicts in place through
`NestedDict.get_or_create_nest`; the model threads the dicts instead (`withNest` walks the key,
runs the caller's step on the nest it reaches, and writes the nest back). The parser never
shares a dict between two places, so the two agree. Errors abort `loads`, so the dicts an
aborted step leaves behind are never seen.

Library calls are parameters:
* `parse_float` is a `ParseFloat`: whether it is `float` itself, and its outcome on each
  string (an exception, a dict or list, or any other object). It is a function of its argument;
  a stateful `parse_float` is out of scope. A float value is stored as `.flt s`, the object
  `parse_float(s)` returned.
* `MAX_KEY_PARTS` (`sys.getrecursionlimit()` at import) and `sys.get_int_max_str_digits()`.
* `int(s, 0)` is modelled on the strings `RE_NUMBER` lets through, with the digit limit of
  `long_from_string_base`, Objects/longobject.c:2960-3041.
* `datetime.date`, `datetime.datetime`, `datetime.time` and `datetime.timezone` are modelled by
  their range checks (Modules/_datetimemodule.c); their messages never escape, since
  `parse_value` replaces every `ValueError` of `match_to_datetime`.

The recursion limit is modelled: `loads` takes `frames`, the value of
`py_recursion_remaining` when it is called (`sys.getrecursionlimit()` minus the number of Python
frames on the stack), and every call of a Python function takes one frame (see `need`).

Scope limits: the regular expressions of `_re.py` are hand-written matchers (they need no
backtracking beyond what the matchers do, see each one); `lru_cache` of `cached_tz` only
memoizes, and `timezone(timedelta(0))` is `timezone.utc`, so an offset is a number of minutes.
Whether the cache already holds an offset only changes the frames `match_to_datetime` needs; it is
the parameter `tzCached`, fixed for one call of `loads` (a document whose first datetime with a
new offset fills the cache for a later one is out of scope). `_re`'s names are taken as already
imported: `__lazy_modules__` (_parser.py:9) makes the first parse that reaches a date, time or
number run the import machinery's frames. Loops and the mutual recursion run on fuel that `loads`
makes large enough (`PyExc.modelFuel` is never a Python outcome).
-/

namespace PyLean.TextLibs.Toml

open PyLean

abbrev Str := List Nat
abbrev Key := List Str

/-- Code points of a Lean string literal. -/
def S (s : String) : Str := s.toList.map Char.toNat

def toS (s : Str) : String := UnicodeObj.toLeanString s

/-! ## Character sets, _parser.py:39-57 -/

def inR (lo hi c : Nat) : Bool := decide (lo ≤ c) && decide (c ≤ hi)

/-- `ASCII_CTRL`, _parser.py:39. -/
def asciiCtrl (c : Nat) : Bool := decide (c < 32) || c == 127
/-- `ILLEGAL_BASIC_STR_CHARS` (also literal strings and comments), _parser.py:43, 46, 49. -/
def illegalBasic (c : Nat) : Bool := asciiCtrl c && c != 9
/-- `ILLEGAL_MULTILINE_BASIC_STR_CHARS` (also multi-line literal strings), _parser.py:44, 47. -/
def illegalMl (c : Nat) : Bool := asciiCtrl c && c != 9 && c != 10
/-- `TOML_WS`, _parser.py:51. -/
def tomlWs (c : Nat) : Bool := c == 32 || c == 9
/-- `TOML_WS_AND_NEWLINE`, _parser.py:52. -/
def tomlWsNl (c : Nat) : Bool := tomlWs c || c == 10
/-- `BARE_KEY_CHARS`, _parser.py:53-55. -/
def bareKey (c : Nat) : Bool := inR 97 122 c || inR 65 90 c || inR 48 57 c || c == 45 || c == 95
/-- `KEY_INITIAL_CHARS`, _parser.py:56. -/
def keyInitial (c : Nat) : Bool := bareKey c || c == 34 || c == 39
/-- `HEXDIGIT_CHARS`, _parser.py:57. -/
def hexDigit (c : Nat) : Bool := inR 97 102 c || inR 65 70 c || inR 48 57 c

/-- `BASIC_STR_ESCAPE_REPLACEMENTS`, _parser.py:59-70, indexed by the character after `\`. -/
def escRepl : Str → Option Nat
  | [92, 98] => some 0x08
  | [92, 116] => some 0x09
  | [92, 110] => some 0x0a
  | [92, 102] => some 0x0c
  | [92, 114] => some 0x0d
  | [92, 101] => some 0x1b
  | [92, 34] => some 0x22
  | [92, 92] => some 0x5c
  | _ => none

/-! ## List helpers with Python's semantics -/

/-- `src[a:b]` for `0 ≤ a`, `0 ≤ b`. -/
def sl (src : Str) (a b : Nat) : Str := (src.drop a).take (b - a)

/-- `src.startswith(p, pos)` for a non-empty `p`. -/
def startsAt (src : Str) (pos : Nat) (p : Str) : Bool := p.isPrefixOf (src.drop pos)

/-- The index of the first occurrence of `pat` in `s`. -/
def findSub (pat : Str) : Str → Option Nat
  | [] => if pat = [] then some 0 else none
  | c :: r => if pat.isPrefixOf (c :: r) then some 0 else (findSub pat r).map (· + 1)

/-- The first index whose character satisfies `p`. -/
def firstIdx (p : Nat → Bool) : Str → Option Nat
  | [] => none
  | c :: r => if p c then some 0 else (firstIdx p r).map (· + 1)

/-- The index of the last `c` in `s`. -/
def lastIdx (c : Nat) (s : Str) : Option Nat :=
  (firstIdx (· == c) s.reverse).map (fun i => s.length - 1 - i)

/-- `repr(s)`. -/
def reprS (s : Str) : Str := UnicodeObj.unicodeRepr s

/-- `str(key)` for a tuple of strings: `('a',)`, `('a', 'b')`. -/
def keyRepr (key : Key) : Str :=
  match key with
  | [] => S "()"
  | [k] => S "(" ++ reprS k ++ S ",)"
  | k :: ks => S "(" ++ reprS k ++ (ks.flatMap (fun x => S ", " ++ reprS x)) ++ S ")"

/-- Association-list dict: `d[k]`. -/
def dget {α : Type} (d : List (Str × α)) (k : Str) : Option α := d.lookup k

/-- `d[k] = v`: replaces in place when present, else appends. -/
def dset {α : Type} (d : List (Str × α)) (k : Str) (v : α) : List (Str × α) :=
  if (d.lookup k).isSome then d.map (fun p => if p.1 == k then (k, v) else p) else d ++ [(k, v)]

/-- `d.pop(k, None)`. -/
def dpop {α : Type} (d : List (Str × α)) (k : Str) : List (Str × α) := d.filter (fun p => p.1 != k)

/-! ## `TOMLDecodeError.__init__`, _parser.py:89-136 -/

/-- An argument of `TOMLDecodeError(...)`: the `DEPRECATED_DEFAULT` sentinel, a `str`, an `int`,
or another object. -/
inductive EArg where
  | dflt
  | str (s : Str)
  | int (i : Int)
  | obj (tag : Str)
  deriving Repr, DecidableEq, Inhabited

def EArg.isStr : EArg → Bool
  | .str _ => true
  | _ => false

def EArg.isInt : EArg → Bool
  | .int _ => true
  | _ => false

/-- The attributes the non-deprecated path sets. -/
structure TdeFull where
  errmsg : Str
  msg : Str
  doc : Str
  pos : Int
  lineno : Nat
  colno : Int
  deriving Repr, DecidableEq, Inhabited

/-- What `__init__` did: the deprecated path calls `ValueError.__init__(self, *args)`. -/
inductive TdeInit where
  | legacy (args : List EArg)
  | full (r : TdeFull)
  deriving Repr, DecidableEq, Inhabited

/-- The `end` argument of `str.count(sub, 0, end)` and `str.rindex(sub, 0, end)` after slice
normalisation (Objects/unicodeobject.c `ADJUST_INDICES`). -/
def sliceEnd (pos : Int) (len : Nat) : Nat :=
  if pos < 0 then (len + pos).toNat else min pos.toNat len

def warnMsg : String :=
  "Free-form arguments for TOMLDecodeError are deprecated. " ++
  "Please set 'msg' (str), 'doc' (str) and 'pos' (int) arguments only."

/-- Lines 119-136 for a `str` msg and doc and an `int` pos. -/
def tdeFull (msg doc : Str) (pos : Int) : Py TdeFull := do
  let pre := doc.take (sliceEnd pos doc.length)
  -- lineno = doc.count("\n", 0, pos) + 1
  let lineno := pre.count 10 + 1
  let colno ← if lineno == 1 then pure (pos + 1)
    else match lastIdx 10 pre with
      | some i => pure (pos - i)
      | none => .error (.valueError "substring not found")
  let coord : Str :=
    if pos ≥ doc.length then S "end of document"
    else S s!"line {lineno}, column {colno}"
  let errmsg := msg ++ S " (at " ++ coord ++ S ")"
  pure { errmsg, msg, doc, pos, lineno, colno }

/-- `TOMLDecodeError.__init__(self, msg, doc, pos, *args)`, _parser.py:89-136. `warnErr` is
whether the warnings filter turns the `DeprecationWarning` into an exception. -/
def tdeInit (warnErr : Bool) (msg doc pos : EArg) (args : List EArg) : Py TdeInit :=
  match args, msg, doc, pos with
  -- `not args and isinstance(msg, str) and isinstance(doc, str) and isinstance(pos, int)`
  | [], .str m, .str d, .int p => (tdeFull m d p).map .full
  | _, _, _, _ =>
    if warnErr then .error (.named "DeprecationWarning" warnMsg)
    else
      let args := if pos != .dflt then pos :: args else args
      let args := if doc != .dflt then doc :: args else args
      let args := if msg != .dflt then msg :: args else args
      .ok (.legacy args)

/-- A raised `TOMLDecodeError`, as `.named "TOMLDecodeError" m`: `m` is `str(e)`, a NUL (which
`str(e)` never holds: the parser's messages are fixed text or a `repr`), then `e.pos` in decimal.
`e.msg` and `e.doc` are the arguments, and `e.lineno` and `e.colno` follow from `doc` and `pos`
(`TdeCoords`). -/
def tdeExc (errmsg : Str) (pos : Nat) : PyExc :=
  .named "TOMLDecodeError" (toS errmsg ++ "\x00" ++ toString pos)

/-- `raise TOMLDecodeError(msg, src, pos)` from inside the parser. -/
def tde (msg : Str) (src : Str) (pos : Nat) : PyExc :=
  match tdeFull msg src pos with
  | .ok r => tdeExc r.errmsg pos
  | .error e => e

def tdeS (msg : String) (src : Str) (pos : Nat) : PyExc := tde (S msg) src pos

/-! ## Values and `parse_float` -/

/-- A value the parser produces. `datetime` carries its offset in minutes (`none` for a local
date-time). `flt s` is the object `parse_float(s)` returned. -/
inductive TVal where
  | str (s : Str)
  | int (i : Int)
  | flt (s : Str)
  | bool (b : Bool)
  | date (y m d : Nat)
  | datetime (y mo d h mi s us : Nat) (tz : Option Int)
  | time (h mi s us : Nat)
  | arr (xs : List TVal)
  | tbl (kvs : List (Str × TVal))
  deriving Repr, Inhabited

abbrev Dict := List (Str × TVal)

/-- `isinstance(value, (dict, list))`. -/
def TVal.isDictOrList : TVal → Bool
  | .arr _ | .tbl _ => true
  | _ => false

/-- What one call of the user's `parse_float` does, when it returns. -/
inductive PfOut where
  | dictOrList
  | other
  deriving Repr, DecidableEq, Inhabited

structure ParseFloat where
  /-- `parse_float is float`. -/
  isFloat : Bool
  call : Str → Py PfOut
  /-- The most Python frames one call on this string pushes (its own included): `0` for a C
  callable such as `float` or `decimal.Decimal`. The callable is assumed not to catch
  `RecursionError`. -/
  frames : Str → Nat := fun _ => 0

/-- `make_safe_parse_float(parse_float)`, _parser.py:758-776: the decorated callable. -/
def makeSafeParseFloat (pf : ParseFloat) : Str → Py Unit :=
  if pf.isFloat then fun s => (pf.call s).map (fun _ => ())
  else fun s => do
    let v ← pf.call s
    match v with
    | .dictOrList => .error (.valueError "parse_float must not return dicts or lists")
    | .other => pure ()

/-- The frames one call of the decorated callable pushes: `float` itself is C (:767-768);
`safe_parse_float` is a Python function (:770-774) that calls `parse_float`. -/
def makeSafeParseFloatN (pf : ParseFloat) (s : Str) : Nat :=
  if pf.isFloat then 0 else 1 + pf.frames s

/-- Whether `cached_tz`'s `lru_cache` already holds `(hour_str, minute_str, sign_str)`. -/
abbrev TzCache := Str → Str → Nat → Bool

structure Cfg where
  /-- The decorated `parse_float`. -/
  pf : Str → Py Unit
  /-- The frames one call of it pushes. -/
  pfN : Str → Nat
  /-- `MAX_KEY_PARTS`, _parser.py:37. -/
  maxKeyParts : Nat
  /-- `sys.get_int_max_str_digits()`; `0` is no limit. -/
  maxStrDigits : Nat
  tzCached : TzCache

/-! ## The recursion limit

Calling a Python function pushes a frame: `_Py_EnterRecursivePy` (Python/ceval_macros.h:426-429,
run at `start_frame`, Python/bytecodes.c:6579-6583) decrements `py_recursion_remaining` and, when
it was not positive, raises `RecursionError("maximum recursion depth exceeded")`
(`_Py_CheckRecursiveCallPy`, Python/ceval.c:1025-1043); returning gives the frame back. C
functions (`str` methods, `int`, `float`, `chr`, regular expressions, `datetime`, the
`lru_cache` wrapper, exception classes) push none.

Every function of the parser except the recursive ones and the statement loop is pure and
catches no `RecursionError`, so it raises `RecursionError` exactly when the deepest chain of
calls it makes on its input needs more frames than are left. `fooN` is that depth for `foo`,
its own frame included, and `need` checks it where `foo` is called. Raising `TOMLDecodeError`
runs its `__init__` (_parser.py:89-136), a Python frame that calls only C functions. A call
that needs one frame is checked only where nothing before it already needed one. -/

def recErr : PyExc := .named "RecursionError" "maximum recursion depth exceeded"

/-- A call that pushes at most `n` frames, made with `r` frames left. -/
def need {α : Type} (r n : Nat) (x : Py α) : Py α := if n ≤ r then x else .error recErr

/-! ## Scanning, _parser.py:320-369 -/

/-- `skip_chars`, _parser.py:320-326: `while src[pos] in chars: pos += 1`. -/
def skipChars (src : Str) (pos : Nat) (p : Nat → Bool) : Nat :=
  pos + ((src.drop pos).takeWhile p).length

/-- `skip_until`, _parser.py:329-348. -/
def skipUntil (src : Str) (pos : Nat) (expect : Str) (errorOn : Nat → Bool) (errorOnEof : Bool) :
    Py Nat :=
  let check (newPos : Nat) : Py Nat :=
    match firstIdx errorOn (sl src pos newPos) with
    | some i =>
      let p := pos + i
      .error (tde (S "Found invalid character " ++ reprS [src.getD p 0]) src p)
    | none => .ok newPos
  match findSub expect (src.drop pos) with
  | some i => check (pos + i)
  | none =>
    if errorOnEof then .error (tde (S "Expected " ++ reprS expect) src src.length)
    else check src.length

/-- Frames `skip_until` pushes: its own, and the error's `__init__` when it raises. -/
def skipUntilN (src : Str) (pos : Nat) (expect : Str) (errorOn : Nat → Bool) (errorOnEof : Bool) : Nat :=
  match skipUntil src pos expect errorOn errorOnEof with
  | .ok _ => 1
  | .error _ => 2

/-- `skip_comment`, _parser.py:351-360. -/
def skipComment (src : Str) (pos : Nat) : Py Nat :=
  if src[pos]? == some 35 then skipUntil src (pos + 1) [10] illegalBasic false
  else .ok pos

def skipCommentN (src : Str) (pos : Nat) : Nat :=
  if src[pos]? == some 35 then 1 + skipUntilN src (pos + 1) [10] illegalBasic false else 1

/-- `skip_comments_and_array_ws`, _parser.py:363-369. -/
def skipCaw (src : Str) : Nat → Nat → Py Nat
  | 0, _ => .error .modelFuel
  | fuel + 1, pos => do
    let before := pos
    let pos := skipChars src pos tomlWsNl
    let pos ← skipComment src pos
    if pos == before then pure pos else skipCaw src fuel pos

def skipCawF (src : Str) (pos : Nat) : Py Nat := skipCaw src (src.length + 1) pos

/-- The deepest call the loop of `skip_comments_and_array_ws` makes in its rounds: `skip_chars`
(one frame) and `skip_comment`. -/
def skipCawNAux (src : Str) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, pos =>
    let p := skipChars src pos tomlWsNl
    let n := max 1 (skipCommentN src p)
    match skipComment src p with
    | .error _ => n
    | .ok q => if q == pos then n else max n (skipCawNAux src fuel q)

def skipCawN (src : Str) (pos : Nat) : Nat := 1 + skipCawNAux src (src.length + 1) pos

/-! ## Strings, _parser.py:566-683 -/

/-- `is_unicode_scalar_value`, _parser.py:754-755. -/
def isScalar (cp : Nat) : Bool := (decide (cp ≤ 55295)) || (decide (57344 ≤ cp) && decide (cp ≤ 1114111))

def hexVal (c : Nat) : Nat :=
  if inR 48 57 c then c - 48 else if inR 97 102 c then c - 87 else c - 55

/-- `int(s, 16)` on a non-empty run of hex digits. -/
def hexInt (s : Str) : Nat := s.foldl (fun a c => a * 16 + hexVal c) 0

/-- `parse_hex_char`, _parser.py:601-611. -/
def parseHexChar (src : Str) (pos hexLen : Nat) : Py (Nat × Str) :=
  let hexStr := sl src pos (pos + hexLen)
  if hexStr.length != hexLen || !hexStr.all hexDigit then .error (tdeS "Invalid hex value" src pos)
  else
    let pos := pos + hexLen
    let hexI := hexInt hexStr
    if !isScalar hexI then .error (tdeS "Escaped character is not a Unicode scalar value" src pos)
    else .ok (pos, [hexI])

/-- `parse_basic_str_escape`, _parser.py:566-594. -/
def parseBasicStrEscape (src : Str) (pos : Nat) (multiline : Bool) : Py (Nat × Str) :=
  let escId := sl src pos (pos + 2)
  let pos := pos + 2
  if multiline && (escId == [92, 32] || escId == [92, 9] || escId == [92, 10]) then
    if escId != [92, 10] then
      let pos := skipChars src pos tomlWs
      match src[pos]? with
      | none => .ok (pos, [])
      | some c =>
        if c != 10 then .error (tdeS "Unescaped '\\' in a string" src pos)
        else .ok (skipChars src (pos + 1) tomlWsNl, [])
    else .ok (skipChars src pos tomlWsNl, [])
  else if escId == [92, 120] then parseHexChar src pos 2
  else if escId == [92, 117] then parseHexChar src pos 4
  else if escId == [92, 85] then parseHexChar src pos 8
  else match escRepl escId with
    | some c => .ok (pos, [c])
    | none => .error (tdeS "Unescaped '\\' in a string" src pos)

/-- `parse_basic_str_escape_multiline`, _parser.py:597-598. -/
def parseBasicStrEscapeMl (src : Str) (pos : Nat) : Py (Nat × Str) :=
  parseBasicStrEscape src pos true

/-- Frames `parse_hex_char` pushes: its own, then `is_unicode_scalar_value` (:607) or the
`__init__` of the error at :604 or :608. -/
def parseHexCharN : Nat := 2

/-- Frames `parse_basic_str_escape` pushes: its own; below it `skip_chars` or an error's
`__init__` on the whitespace branch (:574-584), `parse_hex_char` (:585-590), nothing for a
`frozendict` lookup (:592), an error's `__init__` (:594). -/
def parseBasicStrEscapeN (src : Str) (pos : Nat) (multiline : Bool) : Nat :=
  let escId := sl src pos (pos + 2)
  1 + (if multiline && (escId == [92, 32] || escId == [92, 9] || escId == [92, 10]) then 1
    else if escId == [92, 120] || escId == [92, 117] || escId == [92, 85] then parseHexCharN
    else if (escRepl escId).isSome then 0 else 1)

/-- The loop of `parse_basic_str`, _parser.py:663-683. -/
def basicStrLoop (src : Str) (multiline : Bool) : Nat → Nat → Nat → Str → Py (Nat × Str)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, pos, startPos, result =>
    match src[pos]? with
    | none => .error (tdeS "Unterminated string" src pos)
    | some c =>
      if c == 34 then
        if !multiline then .ok (pos + 1, result ++ sl src startPos pos)
        else if startsAt src pos [34, 34, 34] then .ok (pos + 3, result ++ sl src startPos pos)
        else basicStrLoop src multiline fuel (pos + 1) startPos result
      else if c == 92 then do
        let result := result ++ sl src startPos pos
        let (pos, esc) ← if multiline then parseBasicStrEscapeMl src pos
          else parseBasicStrEscape src pos false
        basicStrLoop src multiline fuel pos pos (result ++ esc)
      else if (if multiline then illegalMl c else illegalBasic c) then
        .error (tde (S "Illegal character " ++ reprS [c]) src pos)
      else basicStrLoop src multiline fuel (pos + 1) startPos result

/-- `parse_basic_str`, _parser.py:654-683. -/
def parseBasicStr (src : Str) (pos : Nat) (multiline : Bool) : Py (Nat × Str) :=
  basicStrLoop src multiline (src.length + 1) pos pos []

/-- The deepest call of the loop of `parse_basic_str`: the escape parser (through the
`_multiline` wrapper, one more frame, when `multiline`) or an error's `__init__`. -/
def basicStrNAux (src : Str) (multiline : Bool) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, pos =>
    match src[pos]? with
    | none => 1
    | some c =>
      if c == 34 then
        if !multiline then 0
        else if startsAt src pos [34, 34, 34] then 0
        else basicStrNAux src multiline fuel (pos + 1)
      else if c == 92 then
        let n := if multiline then 1 + parseBasicStrEscapeN src pos true
          else parseBasicStrEscapeN src pos false
        match (if multiline then parseBasicStrEscapeMl src pos else parseBasicStrEscape src pos false) with
        | .error _ => n
        | .ok (p, _) => max n (basicStrNAux src multiline fuel p)
      else if (if multiline then illegalMl c else illegalBasic c) then 1
      else basicStrNAux src multiline fuel (pos + 1)

def parseBasicStrN (src : Str) (pos : Nat) (multiline : Bool) : Nat :=
  1 + basicStrNAux src multiline (src.length + 1) pos

/-- `parse_one_line_basic_str`, _parser.py:503-505. -/
def parseOneLineBasicStr (src : Str) (pos : Nat) : Py (Nat × Str) :=
  parseBasicStr src (pos + 1) false

def parseOneLineBasicStrN (src : Str) (pos : Nat) : Nat := 1 + parseBasicStrN src (pos + 1) false

/-- `parse_literal_str`, _parser.py:614-620. -/
def parseLiteralStr (src : Str) (pos : Nat) : Py (Nat × Str) := do
  let pos := pos + 1
  let startPos := pos
  let pos ← skipUntil src pos [39] illegalBasic true
  pure (pos + 1, sl src startPos pos)

def parseLiteralStrN (src : Str) (pos : Nat) : Nat := 1 + skipUntilN src (pos + 1) [39] illegalBasic true

/-- `parse_multiline_str`, _parser.py:623-651. -/
def parseMultilineStr (src : Str) (pos : Nat) (literal : Bool) : Py (Nat × Str) := do
  let pos := pos + 3
  let pos := if startsAt src pos [10] then pos + 1 else pos
  let (delim, pos, result) ← if literal then do
      let endPos ← skipUntil src pos [39, 39, 39] illegalMl true
      pure (39, endPos + 3, sl src pos endPos)
    else do
      let (p, r) ← parseBasicStr src pos true
      pure (34, p, r)
  if !startsAt src pos [delim] then return (pos, result)
  let pos := pos + 1
  if !startsAt src pos [delim] then return (pos, result ++ [delim])
  let pos := pos + 1
  return (pos, result ++ [delim, delim])

def parseMultilineStrN (src : Str) (pos : Nat) (literal : Bool) : Nat :=
  let pos := pos + 3
  let pos := if startsAt src pos [10] then pos + 1 else pos
  1 + (if literal then skipUntilN src pos [39, 39, 39] illegalMl true else parseBasicStrN src pos true)

/-! ## `_re.py` -/

def isDigit (c : Nat) : Bool := inR 48 57 c
def isBin (c : Nat) : Bool := c == 48 || c == 49
def isOct (c : Nat) : Bool := inR 48 55 c

/-- `(?:_?D)*`, greedy: the length it matches. An iteration that sees `_` not followed by `D`
fails, and the star stops before the `_`. -/
def usRun (d : Nat → Bool) : Str → Nat
  | [] => 0
  | c :: r =>
    if d c then usRun d r + 1
    else if c == 95 then
      match r with
      | c2 :: r2 => if d c2 then usRun d r2 + 2 else 0
      | [] => 0
    else 0

/-- `D(?:_?D)*`. -/
def dRun (d : Nat → Bool) : Str → Option Nat
  | c :: r => if d c then some (usRun d r + 1) else none
  | [] => none

/-- A match of `RE_NUMBER`: its length, and whether the group `floatpart` is a non-empty
string (`None` for the hex/bin/oct branch). -/
structure NumM where
  len : Nat
  floatpart : Bool
  deriving Repr, DecidableEq

/-- `RE_NUMBER.match(src, pos)`, _re.py:26-44, on `src[pos:]`. Every repetition is followed only
by optional parts that cannot start with what it repeats, so the greedy choice is the match. -/
def matchNumber (s : Str) : Option NumM :=
  let alt1 : Option Nat :=
    match s with
    | 48 :: 120 :: r => (dRun hexDigit r).map (· + 2)
    | 48 :: 98 :: r => (dRun isBin r).map (· + 2)
    | 48 :: 111 :: r => (dRun isOct r).map (· + 2)
    | _ => none
  match alt1 with
  | some n => some ⟨n, false⟩
  | none =>
    let sg := match s with
      | 43 :: _ | 45 :: _ => 1
      | _ => 0
    let s1 := s.drop sg
    let ip : Option Nat :=
      match s1 with
      | 48 :: _ => some 1
      | c :: r => if inR 49 57 c then some (usRun isDigit r + 1) else none
      | [] => none
    match ip with
    | none => none
    | some ipn =>
      let s2 := s1.drop ipn
      let fr : Nat :=
        match s2 with
        | 46 :: r => ((dRun isDigit r).map (· + 1)).getD 0
        | _ => 0
      let s3 := s2.drop fr
      let ex : Nat :=
        match s3 with
        | e :: r =>
          if e == 101 || e == 69 then
            let es := match r with
              | 43 :: _ | 45 :: _ => 1
              | _ => 0
            ((dRun isDigit (r.drop es)).map (· + 1 + es)).getD 0
          else 0
        | [] => 0
      some ⟨sg + ipn + fr + ex, fr + ex > 0⟩

/-- Value of a run of digits and underscores in `base`. -/
def digitsVal (base : Nat) (s : Str) : Nat :=
  (s.filter (· != 95)).foldl (fun a c => a * base + hexVal c) 0

def limitMsg (lim digits : Nat) : String :=
  s!"Exceeds the limit ({lim} digits) for integer string conversion: value has {digits} digits; " ++
  "use sys.set_int_max_str_digits() to increase the limit"

/-- `int(s, 0)` on a string `RE_NUMBER` matched without `floatpart`. The prefixes select a power
of two base, which has no digit limit; a decimal string over the limit raises,
Objects/longobject.c:3024-3033. -/
def intBase0 (maxStrDigits : Nat) (s : Str) : Py Int :=
  match s with
  | 48 :: 120 :: r => .ok (digitsVal 16 r)
  | 48 :: 98 :: r => .ok (digitsVal 2 r)
  | 48 :: 111 :: r => .ok (digitsVal 8 r)
  | _ =>
    let (neg, body) : Bool × Str :=
      match s with
      | 45 :: r => (true, r)
      | 43 :: r => (false, r)
      | _ => (false, s)
    let digits := (body.filter (· != 95)).length
    if digits > 640 && maxStrDigits > 0 && digits > maxStrDigits then
      .error (.valueError (limitMsg maxStrDigits digits))
    else
      let v : Int := digitsVal 10 body
      .ok (if neg then -v else v)

/-- `match_to_number`, _re.py:116-119. -/
def matchToNumber (cfg : Cfg) (group : Str) (m : NumM) : Py TVal :=
  if m.floatpart then do cfg.pf group; pure (.flt group)
  else (intBase0 cfg.maxStrDigits group).map .int

/-- Frames `match_to_number` pushes: its own and `parse_float`'s (`int` is C). -/
def matchToNumberN (cfg : Cfg) (group : Str) (m : NumM) : Nat :=
  1 + if m.floatpart then cfg.pfN group else 0

/-- `([01][0-9]|2[0-3])`. -/
def hourOk (a b : Nat) : Bool := ((a == 48 || a == 49) && isDigit b) || (a == 50 && inR 48 51 b)
/-- `([0-5][0-9])`. -/
def sixtyOk (a b : Nat) : Bool := inR 48 53 a && isDigit b

/-- A match of `_TIME_RE_STR`: the digit strings of its groups and its length. -/
structure TimeM where
  hour : Str
  minute : Str
  sec : Option Str
  frac : Option Str
  len : Nat
  deriving Repr, DecidableEq

/-- `(?:\.([0-9]{1,6})[0-9]*)?`: the captured digits and the length. -/
def matchFrac : Str → Option (Str × Nat)
  | 46 :: r =>
    let ds := r.takeWhile isDigit
    if ds.isEmpty then none else some (ds.take 6, ds.length + 1)
  | _ => none

/-- `_TIME_RE_STR`, _re.py:17-24 (`RE_LOCALTIME.match`). -/
def matchTime : Str → Option TimeM
  | h1 :: h2 :: 58 :: m1 :: m2 :: r =>
    if hourOk h1 h2 && sixtyOk m1 m2 then
      match r with
      | 58 :: s1 :: s2 :: r2 =>
        if sixtyOk s1 s2 then
          match matchFrac r2 with
          | some (f, n) => some ⟨[h1, h2], [m1, m2], some [s1, s2], some f, 8 + n⟩
          | none => some ⟨[h1, h2], [m1, m2], some [s1, s2], none, 8⟩
        else some ⟨[h1, h2], [m1, m2], none, none, 5⟩
      | _ => some ⟨[h1, h2], [m1, m2], none, none, 5⟩
    else none
  | _ => none

/-- The offset groups of `RE_DATETIME`. -/
inductive OffM where
  | none
  | zulu
  | ofs (sign : Nat) (h m : Str)
  deriving Repr, DecidableEq

/-- `(?:([Zz])|([+-])([01][0-9]|2[0-3]):([0-5][0-9]))?`, _re.py:52. -/
def matchOffset (s : Str) : OffM × Nat :=
  match s with
  | z :: r =>
    if z == 90 || z == 122 then (.zulu, 1)
    else if z == 43 || z == 45 then
      match r with
      | h1 :: h2 :: 58 :: m1 :: m2 :: _ =>
        if hourOk h1 h2 && sixtyOk m1 m2 then (.ofs z [h1, h2] [m1, m2], 6) else (.none, 0)
      | _ => (.none, 0)
    else (.none, 0)
  | [] => (.none, 0)

structure DtM where
  year : Str
  month : Str
  day : Str
  time : Option (TimeM × OffM)
  len : Nat
  deriving Repr, DecidableEq

def monthOk (a b : Nat) : Bool := (a == 48 && inR 49 57 b) || (a == 49 && inR 48 50 b)
def dayOk (a b : Nat) : Bool :=
  (a == 48 && inR 49 57 b) || ((a == 49 || a == 50) && isDigit b) || (a == 51 && inR 48 49 b)

/-- `RE_DATETIME.match`, _re.py:46-56. The time part is optional as a whole, so a failed time
leaves the date alone. -/
def matchDatetime : Str → Option DtM
  | y1 :: y2 :: y3 :: y4 :: 45 :: mo1 :: mo2 :: 45 :: d1 :: d2 :: r =>
    if isDigit y1 && isDigit y2 && isDigit y3 && isDigit y4 && monthOk mo1 mo2 && dayOk d1 d2 then
      let tm : Option (TimeM × OffM × Nat) :=
        match r with
        | sep :: r2 =>
          if sep == 84 || sep == 116 || sep == 32 then
            match matchTime r2 with
            | some t =>
              let (o, n) := matchOffset (r2.drop t.len)
              some (t, o, 1 + t.len + n)
            | none => none
          else none
        | [] => none
      match tm with
      | some (t, o, n) => some ⟨[y1, y2, y3, y4], [mo1, mo2], [d1, d2], some (t, o), 10 + n⟩
      | none => some ⟨[y1, y2, y3, y4], [mo1, mo2], [d1, d2], none, 10⟩
    else none
  | _ => none

/-- `int(s)` on ASCII digits. -/
def decInt (s : Str) : Nat := s.foldl (fun a c => a * 10 + (c - 48)) 0

def isLeap (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeap y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- `check_date_args`, Modules/_datetimemodule.c. -/
def checkDate (y m d : Nat) : Py Unit :=
  if y < 1 || y > 9999 then .error (.valueError s!"~year {y} is out of range")
  else if m < 1 || m > 12 then .error (.valueError "month must be in 1..12")
  else if d < 1 || d > daysInMonth y m then .error (.valueError "~day is out of range for month")
  else .ok ()

/-- `check_time_args`, Modules/_datetimemodule.c. -/
def checkTime (h mi s us : Nat) : Py Unit :=
  if h > 23 then .error (.valueError "hour must be in 0..23")
  else if mi > 59 then .error (.valueError "minute must be in 0..59")
  else if s > 59 then .error (.valueError "second must be in 0..59")
  else if us > 999999 then .error (.valueError "microsecond must be in 0..999999")
  else .ok ()

/-- `cached_tz`, _re.py:98-106: `timezone(timedelta(hours=±h, minutes=±m))` as minutes. -/
def cachedTz (hourStr minuteStr : Str) (sign : Nat) : Py Int :=
  let sg : Int := if sign == 43 then 1 else -1
  let off : Int := sg * (decInt hourStr : Int) * 60 + sg * (decInt minuteStr : Int)
  if off.natAbs ≥ 24 * 60 then
    .error (.valueError "~offset must be a timedelta strictly between -timedelta(hours=24) and timedelta(hours=24).")
  else .ok off

/-- `micros_str.ljust(6, "0")`. -/
def ljust6 (s : Str) : Str := s ++ List.replicate (6 - s.length) 48

/-- `match_to_datetime`, _re.py:59-92. -/
def matchToDatetime (m : DtM) : Py TVal := do
  let year := decInt m.year
  let month := decInt m.month
  let day := decInt m.day
  match m.time with
  | none => do checkDate year month day; pure (.date year month day)
  | some (t, off) =>
    let hour := decInt t.hour
    let minute := decInt t.minute
    let sec := match t.sec with
      | some s => if s.isEmpty then 0 else decInt s
      | none => 0
    let micros := match t.frac with
      | some f => if f.isEmpty then 0 else decInt (ljust6 f)
      | none => 0
    let tz ← match off with
      | .ofs sg h mm => some <$> cachedTz h mm sg
      | .zulu => pure (some 0)
      | .none => pure none
    checkDate year month day
    checkTime hour minute sec micros
    pure (.datetime year month day hour minute sec micros tz)

/-- Frames `match_to_datetime` pushes: its own, and `cached_tz`'s when the `lru_cache` (a C
wrapper) does not hold the offset. -/
def matchToDatetimeN (tzCached : TzCache) (m : DtM) : Nat :=
  1 + match m.time with
    | some (_, .ofs sg h mm) => if tzCached h mm sg then 0 else 1
    | _ => 0

/-- `match_to_localtime`, _re.py:109-113. -/
def matchToLocaltime (t : TimeM) : Py TVal := do
  let sec := match t.sec with
    | some s => if s.isEmpty then 0 else decInt s
    | none => 0
  let micros := match t.frac with
    | some f => if f.isEmpty then 0 else decInt (ljust6 f)
    | none => 0
  checkTime (decInt t.hour) (decInt t.minute) sec micros
  pure (.time (decInt t.hour) (decInt t.minute) sec micros)

/-! ## `Flags`, _parser.py:222-277 -/

/-- One node of `Flags._flags`: `{"flags": set(), "recursive_flags": set(), "nested": {}}`. -/
inductive FNode where
  | mk (flags : List Nat) (rflags : List Nat) (nested : List (Str × FNode))
  deriving Repr, Inhabited

def FNode.flags : FNode → List Nat
  | .mk f _ _ => f
def FNode.rflags : FNode → List Nat
  | .mk _ r _ => r
def FNode.nested : FNode → List (Str × FNode)
  | .mk _ _ n => n
def FNode.empty : FNode := .mk [] [] []

/-- `s.add(x)` on a set of flags. -/
def addFlag (f : Nat) (s : List Nat) : List Nat := if f ∈ s then s else s ++ [f]

def FROZEN : Nat := 0
def EXPLICIT_NEST : Nat := 1

structure Flags where
  /-- `_flags`. -/
  tree : List (Str × FNode) := []
  /-- `_pending_flags`, a set; its iteration order is not observable. -/
  pending : List (Key × Nat) := []
  deriving Repr, Inhabited

/-- `Flags.__init__`, _parser.py:231-233. -/
def Flags.init : Flags := { tree := [], pending := [] }

/-- The walk of `Flags.set` below the root, _parser.py:254-260. -/
def fsetAux (flag : Nat) (recursive : Bool) : Key → List (Str × FNode) → List (Str × FNode)
  | [], cont => cont
  | [stem], cont =>
    let n := (dget cont stem).getD .empty
    let n := match n with
      | .mk f r ns => if recursive then .mk f (addFlag flag r) ns else .mk (addFlag flag f) r ns
    dset cont stem n
  | k :: ks, cont =>
    let n := (dget cont k).getD .empty
    match n with
    | .mk f r ns => dset cont k (.mk f r (fsetAux flag recursive ks ns))

/-- `Flags.set`, _parser.py:251-260. `key[-1]` of an empty key raises `IndexError`. -/
def Flags.set (fl : Flags) (key : Key) (flag : Nat) (recursive : Bool) : Py Flags :=
  if key.isEmpty then .error (.indexError "tuple index out of range")
  else .ok { fl with tree := fsetAux flag recursive key fl.tree }

/-- The walk of `Flags.unset_all`, _parser.py:244-249. -/
def unsetAux : Key → List (Str × FNode) → List (Str × FNode)
  | [], cont => cont
  | [stem], cont => dpop cont stem
  | k :: ks, cont =>
    match dget cont k with
    | none => cont
    | some (.mk f r ns) => dset cont k (.mk f r (unsetAux ks ns))

/-- `Flags.unset_all`, _parser.py:243-249. -/
def Flags.unsetAll (fl : Flags) (key : Key) : Py Flags :=
  if key.isEmpty then .error (.indexError "tuple index out of range")
  else .ok { fl with tree := unsetAux key fl.tree }

/-- The walk of `Flags.is_`, _parser.py:265-277. -/
def isAux (flag : Nat) : Key → List (Str × FNode) → Bool
  | [], _ => false
  | [stem], cont =>
    match dget cont stem with
    | some n => n.flags.contains flag || n.rflags.contains flag
    | none => false
  | k :: ks, cont =>
    match dget cont k with
    | none => false
    | some n => if n.rflags.contains flag then true else isAux flag ks n.nested

/-- `Flags.is_`, _parser.py:262-277. -/
def Flags.is_ (fl : Flags) (key : Key) (flag : Nat) : Bool :=
  if key.isEmpty then false else isAux flag key fl.tree

/-- `Flags.add_pending`, _parser.py:235-236. -/
def Flags.addPending (fl : Flags) (key : Key) (flag : Nat) : Flags :=
  if fl.pending.contains (key, flag) then fl else { fl with pending := fl.pending ++ [(key, flag)] }

/-- `Flags.finalize_pending`, _parser.py:238-241. -/
def Flags.finalizePending (fl : Flags) : Py Flags := do
  let fl' ← fl.pending.foldlM (fun (acc : Flags) (kf : Key × Nat) => acc.set kf.1 kf.2 false) fl
  pure { fl' with pending := [] }

/-! ## `NestedDict`, _parser.py:280-311 -/

def noNest : PyExc := .keyError "There is no nest behind this key"

/-- `NestedDict.get_or_create_nest(key, access_lists=...)`, _parser.py:285-300, followed by the
caller's step `f` on the nest it returns; the nest is written back along the key. -/
def withNest {α : Type} (accessLists : Bool) (f : Dict → Py (Dict × α)) : Key → Dict → Py (Dict × α)
  | [], cont => f cont
  | k :: ks, cont =>
    let cont := if (dget cont k).isSome then cont else dset cont k (.tbl [])
    match dget cont k with
    | some (.tbl d) => do
      let (d', a) ← withNest accessLists f ks d
      pure (dset cont k (.tbl d'), a)
    | some (.arr xs) =>
      if accessLists then
        match xs.getLast? with
        | none => .error (.indexError "list index out of range")
        | some (.tbl d) => do
          let (d', a) ← withNest accessLists f ks d
          pure (dset cont k (.arr (xs.dropLast ++ [.tbl d'])), a)
        | some _ => .error noNest
      else .error noNest
    | _ => .error noNest

/-- `NestedDict.get_or_create_nest(key)` alone. -/
def getOrCreateNest (accessLists : Bool) (key : Key) (d : Dict) : Py Dict :=
  (withNest accessLists (fun c => .ok (c, ())) key d).map (·.1)

/-- `NestedDict.append_nest_to_list`, _parser.py:302-311. -/
def appendNestToList (key : Key) (d : Dict) : Py Dict :=
  (withNest true (fun cont =>
    match key.getLast? with
    | none => .error (.indexError "tuple index out of range")
    | some last =>
      match dget cont last with
      | some (.arr xs) => .ok (dset cont last (.arr (xs ++ [.tbl []])), ())
      | some _ => .error (.keyError "An object other than list found behind this key")
      | none => .ok (dset cont last (.arr [.tbl []]), ())) key.dropLast d).map (·.1)

/-- `Output`, _parser.py:314-317. -/
structure Out where
  data : Dict := []
  flags : Flags := Flags.init
  deriving Repr, Inhabited

/-- `Output.__init__`. -/
def Out.init : Out := { data := [], flags := Flags.init }

/-- `except KeyError: raise TOMLDecodeError("Cannot overwrite a value", src, pos)`. -/
def overwriteErr {α : Type} (src : Str) (pos : Nat) : Py α → Py α
  | .error (.keyError _) => .error (tdeS "Cannot overwrite a value" src pos)
  | r => r

/-! ## Keys, _parser.py:465-500 -/

/-- `parse_key_part`, _parser.py:487-500. -/
def parseKeyPart (src : Str) (pos : Nat) : Py (Nat × Str) :=
  match src[pos]? with
  | some c =>
    if bareKey c then
      let p := skipChars src pos bareKey
      .ok (p, sl src pos p)
    else if c == 39 then parseLiteralStr src pos
    else if c == 34 then parseOneLineBasicStr src pos
    else .error (tdeS "Invalid initial character for a key part" src pos)
  | none => .error (tdeS "Invalid initial character for a key part" src pos)

def parseKeyPartN (src : Str) (pos : Nat) : Nat :=
  1 + match src[pos]? with
    | some c =>
      if bareKey c then 1
      else if c == 39 then parseLiteralStrN src pos
      else if c == 34 then parseOneLineBasicStrN src pos
      else 1
    | none => 1

def keyPartsMsg (n : Nat) : String := s!"TOML key has more than the allowed {n} parts"

/-- The loop of `parse_key`, _parser.py:469-484. -/
def keyLoop (maxKeyParts : Nat) (src : Str) : Nat → Nat → Key → Py (Nat × Key)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, pos, key =>
    if src[pos]? != some 46 then .ok (pos, key)
    else do
      let pos := skipChars src (pos + 1) tomlWs
      let (pos, part) ← parseKeyPart src pos
      let key := key ++ [part]
      if key.length > maxKeyParts then .error (.named "RecursionError" (keyPartsMsg maxKeyParts))
      else keyLoop maxKeyParts src fuel (skipChars src pos tomlWs) key

/-- `parse_key`, _parser.py:465-484. -/
def parseKey (maxKeyParts : Nat) (src : Str) (pos : Nat) : Py (Nat × Key) := do
  let (pos, part) ← parseKeyPart src pos
  let pos := skipChars src pos tomlWs
  keyLoop maxKeyParts src (src.length + 1) pos [part]

/-- The deepest call of the loop of `parse_key`: `skip_chars` (one frame) and `parse_key_part`;
`RecursionError(...)` is a C call. -/
def keyLoopN (maxKeyParts : Nat) (src : Str) : Nat → Nat → Key → Nat
  | 0, _, _ => 0
  | fuel + 1, pos, key =>
    if src[pos]? != some 46 then 0
    else
      let p1 := skipChars src (pos + 1) tomlWs
      let n := max 1 (parseKeyPartN src p1)
      match parseKeyPart src p1 with
      | .error _ => n
      | .ok (p, part) =>
        if (key ++ [part]).length > maxKeyParts then n
        else max n (keyLoopN maxKeyParts src fuel (skipChars src p tomlWs) (key ++ [part]))

/-- Frames `parse_key` pushes (the `skip_chars` after the first part needs one, fewer than
`parse_key_part`). -/
def parseKeyN (maxKeyParts : Nat) (src : Str) (pos : Nat) : Nat :=
  1 + match parseKeyPart src pos with
    | .error _ => parseKeyPartN src pos
    | .ok (p, part) =>
      max (parseKeyPartN src pos) (keyLoopN maxKeyParts src (src.length + 1) (skipChars src p tomlWs) [part])

/-! ## Values, _parser.py:449-462, 508-563, 686-751 -/

mutual

/-- `parse_value`, _parser.py:686-751, with `r` frames left below its own. -/
def parseValue (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → Py (Nat × TVal)
  | 0, _ => .error .modelFuel
  | fuel + 1, pos =>
    let c := src[pos]?
    if c == some 34 then
      if startsAt src pos [34, 34, 34] then
        need r (parseMultilineStrN src pos false) ((parseMultilineStr src pos false).map (fun r => (r.1, .str r.2)))
      else need r (parseOneLineBasicStrN src pos) ((parseOneLineBasicStr src pos).map (fun r => (r.1, .str r.2)))
    else if c == some 39 then
      if startsAt src pos [39, 39, 39] then
        need r (parseMultilineStrN src pos true) ((parseMultilineStr src pos true).map (fun r => (r.1, .str r.2)))
      else need r (parseLiteralStrN src pos) ((parseLiteralStr src pos).map (fun r => (r.1, .str r.2)))
    else if c == some 116 && startsAt src pos (S "true") then .ok (pos + 4, .bool true)
    else if c == some 102 && startsAt src pos (S "false") then .ok (pos + 5, .bool false)
    else if c == some 91 then need r 1 (parseArray cfg src (r - 1) fuel pos)
    else if c == some 123 then need r 1 (parseInlineTable cfg src (r - 1) fuel pos)
    else
      match matchDatetime (src.drop pos) with
      | some m =>
        -- the `__init__` of the error at :730 needs one frame, no more than `match_to_datetime`
        need r (matchToDatetimeN cfg.tzCached m) <|
        match matchToDatetime m with
        | .ok v => .ok (pos + m.len, v)
        | .error (.valueError _) => .error (tdeS "Invalid date or datetime" src pos)
        | .error e => .error e
      | none =>
        match matchTime (src.drop pos) with
        | some t => need r 1 ((matchToLocaltime t).map (fun v => (pos + t.len, v)))
        | none =>
          match matchNumber (src.drop pos) with
          | some m =>
            need r (matchToNumberN cfg (sl src pos (pos + m.len)) m)
              ((matchToNumber cfg (sl src pos (pos + m.len)) m).map (fun v => (pos + m.len, v)))
          | none =>
            let firstThree := sl src pos (pos + 3)
            if firstThree == S "inf" || firstThree == S "nan" then
              need r (cfg.pfN firstThree) (do
                cfg.pf firstThree
                pure (pos + 3, .flt firstThree))
            else
              let firstFour := sl src pos (pos + 4)
              if firstFour == S "-inf" || firstFour == S "+inf" || firstFour == S "-nan" ||
                  firstFour == S "+nan" then
                need r (cfg.pfN firstFour) (do
                  cfg.pf firstFour
                  pure (pos + 4, .flt firstFour))
              else need r 1 (.error (tdeS "Invalid value" src pos))

/-- `parse_array`, _parser.py:508-529, with `r` frames left below its own. -/
def parseArray (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → Py (Nat × TVal)
  | 0, _ => .error .modelFuel
  | fuel + 1, pos => do
    let pos := pos + 1
    let pos ← need r (skipCawN src pos) (skipCawF src pos)
    if startsAt src pos [93] then pure (pos + 1, .arr [])
    else arrayLoop cfg src r fuel pos []

/-- The loop of `parse_array`, _parser.py:515-529. The error's `__init__` at :524 needs one
frame, fewer than the `skip_comments_and_array_ws` before it. -/
def arrayLoop (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → List TVal → Py (Nat × TVal)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, pos, array => do
    let (pos, val) ← need r 1 (parseValue cfg src (r - 1) fuel pos)
    let array := array ++ [val]
    let pos ← need r (skipCawN src pos) (skipCawF src pos)
    let c := sl src pos (pos + 1)
    if c == [93] then return (pos + 1, .arr array)
    if c != [44] then .error (tdeS "Unclosed array" src pos)
    else
      let pos := pos + 1
      let pos ← need r (skipCawN src pos) (skipCawF src pos)
      if startsAt src pos [93] then pure (pos + 1, .arr array)
      else arrayLoop cfg src r fuel pos array

/-- `parse_inline_table`, _parser.py:532-563, with `r` frames left below its own. `NestedDict()`
and `Flags()` (:534-535) run an `__init__` each, one frame, fewer than the
`skip_comments_and_array_ws` after them. -/
def parseInlineTable (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → Py (Nat × TVal)
  | 0, _ => .error .modelFuel
  | fuel + 1, pos => do
    let pos := pos + 1
    let pos ← need r (skipCawN src pos) (skipCawF src pos)
    if startsAt src pos [125] then pure (pos + 1, .tbl [])
    else inlineLoop cfg src r fuel pos [] Flags.init

/-- The loop of `parse_inline_table`, _parser.py:540-563, over `nested_dict.dict` and `flags`.
The `Flags` and `NestedDict` methods and the errors' `__init__` need one frame each, and
`parse_key_value_pair` has just needed more (`parse_key` alone needs three, `parseKeyN_ge`). -/
def inlineLoop (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → Dict → Flags → Py (Nat × TVal)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, pos, data, flags => do
    let (pos, key, value) ← need r 1 (parseKeyValuePair cfg src (r - 1) fuel pos)
    let keyParent := key.dropLast
    let keyStem := key.getLastD []
    if flags.is_ key FROZEN then
      .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr key) src pos)
    else
      let (data, _) ← overwriteErr src pos <| withNest false (fun nest =>
        if (dget nest keyStem).isSome then
          .error (tde (S "Duplicate inline table key " ++ reprS keyStem) src pos)
        else .ok (dset nest keyStem value, ())) keyParent data
      let pos ← need r (skipCawN src pos) (skipCawF src pos)
      let c := sl src pos (pos + 1)
      if c == [125] then return (pos + 1, .tbl data)
      if c != [44] then .error (tdeS "Unclosed inline table" src pos)
      else
        let pos := pos + 1
        let pos ← need r (skipCawN src pos) (skipCawF src pos)
        if startsAt src pos [125] then return (pos + 1, .tbl data)
        let flags ← if value.isDictOrList then flags.set key FROZEN true else pure flags
        inlineLoop cfg src r fuel pos data flags

/-- `parse_key_value_pair`, _parser.py:449-462, with `r` frames left below its own. After
`parse_key`, the error's `__init__` and `skip_chars` need one frame. -/
def parseKeyValuePair (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → Py (Nat × Key × TVal)
  | 0, _ => .error .modelFuel
  | fuel + 1, pos => do
    let (pos, key) ← need r (parseKeyN cfg.maxKeyParts src pos) (parseKey cfg.maxKeyParts src pos)
    if src[pos]? != some 61 then
      .error (tdeS "Expected '=' after a key in a key/value pair" src pos)
    else
      let pos := skipChars src (pos + 1) tomlWs
      let (pos, value) ← need r 1 (parseValue cfg src (r - 1) fuel pos)
      pure (pos, key, value)

end

/-- The fuel `loads` gives `parse_value`: each call consumes fuel and each nesting level and
loop round consumes at least one character. -/
def vFuel (src : Str) : Nat := 4 * src.length + 8

/-! ## Statements, _parser.py:372-446 -/

/-- `create_dict_rule`, _parser.py:372-389. -/
def createDictRule (cfg : Cfg) (src : Str) (pos : Nat) (out : Out) : Py (Nat × Key × Out) := do
  let pos := pos + 1
  let pos := skipChars src pos tomlWs
  let (pos, key) ← parseKey cfg.maxKeyParts src pos
  if out.flags.is_ key EXPLICIT_NEST || out.flags.is_ key FROZEN then
    .error (tde (S "Cannot declare " ++ keyRepr key ++ S " twice") src pos)
  else
    let flags ← out.flags.set key EXPLICIT_NEST false
    let data ← overwriteErr src pos (getOrCreateNest true key out.data)
    if !startsAt src pos [93] then
      .error (tdeS "Expected ']' at the end of a table declaration" src pos)
    else pure (pos + 1, key, { data, flags })

/-- `create_list_rule`, _parser.py:392-412. -/
def createListRule (cfg : Cfg) (src : Str) (pos : Nat) (out : Out) : Py (Nat × Key × Out) := do
  let pos := pos + 2
  let pos := skipChars src pos tomlWs
  let (pos, key) ← parseKey cfg.maxKeyParts src pos
  if out.flags.is_ key FROZEN then
    .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr key) src pos)
  else
    let flags ← out.flags.unsetAll key
    let flags ← flags.set key EXPLICIT_NEST false
    let data ← overwriteErr src pos (appendNestToList key out.data)
    if !startsAt src pos [93, 93] then
      .error (tdeS "Expected ']]' at the end of an array declaration" src pos)
    else pure (pos + 2, key, { data, flags })

/-- Frames `create_dict_rule` (`skip = 1`) and `create_list_rule` (`skip = 2`) push: their own
and `parse_key`'s. Their other calls (`skip_chars`, the `Flags` and `NestedDict` methods,
`append_nest_to_list` and the `get_or_create_nest` it calls, an error's `__init__`) need at most
two, and `parse_key` at least three (`parseKeyN_ge`). -/
def createRuleN (maxKeyParts : Nat) (src : Str) (pos skip : Nat) : Nat :=
  1 + parseKeyN maxKeyParts src (skipChars src (pos + skip) tomlWs)

/-- The `for cont_key in relative_path_cont_keys` loop of `key_value_rule`, _parser.py:422-429. -/
def contKeysLoop (src : Str) (pos : Nat) : List Key → Flags → Py Flags
  | [], fl => .ok fl
  | ck :: cks, fl =>
    if fl.is_ ck EXPLICIT_NEST then
      .error (tde (S "Cannot redefine namespace " ++ keyRepr ck) src pos)
    else contKeysLoop src pos cks (fl.addPending ck EXPLICIT_NEST)

/-- `key_value_rule`, _parser.py:415-446, with `r` frames left below its own. The `Flags` and
`NestedDict` methods and the errors' `__init__` need one frame each, fewer than
`parse_key_value_pair` needed. -/
def keyValueRule (cfg : Cfg) (src : Str) (r : Nat) (pos : Nat) (out : Out) (header : Key) : Py (Nat × Out) := do
  let (pos, key, value) ← need r 1 (parseKeyValuePair cfg src (r - 1) (vFuel src) pos)
  let keyParent := key.dropLast
  let keyStem := key.getLastD []
  let absKeyParent := header ++ keyParent
  let contKeys := (List.range (key.length - 1)).map (fun i => header ++ key.take (i + 1))
  let flags ← contKeysLoop src pos contKeys out.flags
  if flags.is_ absKeyParent FROZEN then
    .error (tde (S "Cannot mutate immutable namespace " ++ keyRepr absKeyParent) src pos)
  else
    let (data, _) ← overwriteErr src pos <| withNest true (fun nest =>
      if (dget nest keyStem).isSome then .error (tdeS "Cannot overwrite a value" src pos)
      else .ok (dset nest keyStem value, ())) absKeyParent out.data
    let flags ← if value.isDictOrList then flags.set (header ++ key) FROZEN true else pure flags
    pure (pos, { data, flags })

/-! ## `loads` and `load`, _parser.py:139-219 -/

/-- `s.replace("\r\n", "\n")`. -/
def crlf : Str → Str
  | 13 :: 10 :: r => 10 :: crlf r
  | c :: r => c :: crlf r
  | [] => []

/-- The statement loop of `loads`, _parser.py:169-217, with `r` frames left below `loads`'s own.
`loads` has checked `r ≥ 3`, more than `skip_chars`, `finalize_pending` (and the `Flags.set` it
calls) and an error's `__init__` need. -/
def mainLoop (cfg : Cfg) (src : Str) (r : Nat) : Nat → Nat → Out → Key → Py Dict
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, pos, out, header =>
    let pos := skipChars src pos tomlWs
    match src[pos]? with
    | none => .ok out.data
    | some c =>
      if c == 10 then mainLoop cfg src r fuel (pos + 1) out header
      else do
        let (pos, out, header) ←
          if keyInitial c then do
            let (p, o) ← need r 1 (keyValueRule cfg src (r - 1) pos out header)
            pure (skipChars src p tomlWs, o, header)
          else if c == 91 then do
            let second := src[pos + 1]?
            let flags ← out.flags.finalizePending
            let out := { out with flags }
            let (p, key, o) ← if second == some 91 then
                need r (createRuleN cfg.maxKeyParts src pos 2) (createListRule cfg src pos out)
              else need r (createRuleN cfg.maxKeyParts src pos 1) (createDictRule cfg src pos out)
            pure (skipChars src p tomlWs, o, key)
          else if c != 35 then .error (tdeS "Invalid statement" src pos)
          else pure (pos, out, header)
        let pos ← need r (skipCommentN src pos) (skipComment src pos)
        match src[pos]? with
        | none => .ok out.data
        | some c =>
          if c != 10 then .error (tdeS "Expected newline or end of document after a statement" src pos)
          else mainLoop cfg src r fuel (pos + 1) out header

/-- The first argument of `loads`: a `str`, or an object whose `replace` raises
`AttributeError` or `TypeError` (its `type(s).__qualname__`). -/
inductive SArg where
  | str (s : Str)
  | other (qualname : String)
  deriving Repr, DecidableEq, Inhabited

/-- The configuration `loads` runs with. -/
def mkCfg (pf : ParseFloat) (maxKeyParts maxStrDigits : Nat) (tzCached : TzCache) : Cfg :=
  { pf := makeSafeParseFloat pf, pfN := makeSafeParseFloatN pf, maxKeyParts, maxStrDigits, tzCached }

/-- `loads(s, parse_float=pf)`, _parser.py:151-219, called with `frames` frames left.

`Output()` (:163) runs `Output.__init__`, which instantiates `NestedDict` and `Flags`. Once the
call site is specialized, `CALL_ALLOC_AND_ENTER_INIT` (Python/bytecodes.c:4815-4823) takes two
frames for an instantiation, an `_Py_InitCleanup` shim and `__init__` (:4790-4813), when at least
two are left (`_CHECK_RECURSION_REMAINING`, :4611-4613), and the generic call takes one
otherwise; so `Output()` succeeds exactly when three are left: the shim, `Output.__init__`, and
one for `NestedDict()`. (Instantiating a class whose `__init__` calls nothing needs one frame
either way.) The model takes the call sites as specialized, which they are after a few calls of
`loads`; on a cold call site two frames suffice. `make_safe_parse_float` (:165) needs one. -/
def loads (pf : ParseFloat) (maxKeyParts maxStrDigits : Nat) (tzCached : TzCache)
    (frames : Nat) (s : SArg) : Py Dict :=
  need frames 1 <|
  match s with
  | .other q => .error (.typeError s!"Expected str object, not '{q}'")
  | .str s =>
    let src := crlf s
    let cfg := mkCfg pf maxKeyParts maxStrDigits tzCached
    need (frames - 1) 3 (mainLoop cfg src (frames - 1) (src.length + 1) 0 Out.init [])

/-- What `fp.read()` returned: `bytes`/`bytearray`, an object without `decode` (a `str` from a
text file), or an object whose `decode()` gives this outcome. -/
inductive ReadVal where
  | bytes (b : List Nat)
  | noDecode
  | custom (decoded : Py SArg)

def binaryModeMsg : String :=
  "File must be opened in binary mode, e.g. use `open('foo.toml', 'rb')`"

/-- `load(fp, parse_float=pf)`, _parser.py:139-148, called with `frames` frames left. `read` is
the outcome of `fp.read()` (the frames it needs are part of that outcome). -/
def load (pf : ParseFloat) (maxKeyParts maxStrDigits : Nat) (tzCached : TzCache)
    (frames : Nat) (read : Py ReadVal) : Py Dict := need frames 1 do
  let b ← read
  let s ← match b with
    | .bytes b => (UnicodeObj.utf8Decode b .strict).map SArg.str
    | .noDecode => .error (.typeError binaryModeMsg)
    | .custom r =>
      match r with
      | .error (.named "AttributeError" _) => .error (.typeError binaryModeMsg)
      | r => r
  loads pf maxKeyParts maxStrDigits tzCached (frames - 1) s

end PyLean.TextLibs.Toml
