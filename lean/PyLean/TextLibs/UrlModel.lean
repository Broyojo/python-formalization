import PyLean.UnicodeObj.CodecProps
import PyLean.UnicodeObj.TextCase

/-!
Model of `Lib/urllib/parse.py`, CPython 3.15.2.

A `str` is a list of code points and a `bytes` a list of byte values. Arguments of the
parsing functions are `Arg`s: `None`, a `str`, or a `bytes`/`bytearray`. Inside the functions,
after `_coerce_args`, a value is a `V`: a `str`, or a `bytes`/`bytearray` that the coercion let
through (only an empty one can be, since a non-empty one raises "Cannot mix"). The few Python
operations the code applies to such values (`+`, `%s`, truth, slicing) are modelled with their
`TypeError`s, so a call that mixes `str` with an empty `bytes` behaves as in CPython.

Two library calls are parameters: `nfkc`, `unicodedata.normalize('NFKC', _)` in `_checknetloc`,
and `ipk`, the outcome of `ipaddress.ip_address(_)` in `_check_bracketed_host`: `none` when it
raises, `some true` for an `IPv4Address`, `some false` for an `IPv6Address`. Properties quantify
over both. The `ValueError` of `ip_address` embeds a repr, so its message starts with `~`.

`encoding` is one of 'utf-8', 'ascii' and 'latin-1' (the codecs of `PyLean.UnicodeObj`); the
error handlers are the registered ones except `namereplace` for 'ascii' and 'latin-1', which needs
the Unicode name database. The deprecated public wrappers (`splittype` and the rest) only warn and
call the private helpers modelled here, which take `str`.
-/

namespace PyLean.TextLibs.Url

open PyLean

abbrev Str := List Nat

/-- Code points of a Lean string literal. -/
def cs (s : String) : Str := s.toList.map Char.toNat

/-- A Lean string of code points, for messages. -/
def toS (s : Str) : String := UnicodeObj.toLeanString s

/-! ## Arguments and values -/

/-- An argument: `None`, a `str`, or a `bytes` (`ba = false`) or `bytearray` (`ba = true`). -/
inductive Arg where
  | none
  | str (s : Str)
  | bytes (b : Str) (ba : Bool)
  deriving Repr, DecidableEq, Inhabited

def Arg.truthy : Arg → Bool
  | .none => false
  | .str s => !s.isEmpty
  | .bytes b _ => !b.isEmpty

def Arg.isStr : Arg → Bool
  | .str _ => true
  | _ => false

/-- A value after `_coerce_args`: a `str`, or a `bytes`/`bytearray` it did not convert. -/
inductive V where
  | s (x : Str)
  | b (x : Str) (ba : Bool)
  deriving Repr, DecidableEq, Inhabited

def bytesTy (ba : Bool) : String := if ba then "bytearray" else "bytes"

def tyName : Option V → String
  | none => "NoneType"
  | some (.s _) => "str"
  | some (.b _ ba) => bytesTy ba

/-- `bool(x)`. -/
def truthy : Option V → Bool
  | none => false
  | some (.s x) => !x.isEmpty
  | some (.b x _) => !x.isEmpty

/-- `x + y`, with the `TypeError`s of `unicode_concatenate` and `bytes_concat`. -/
def add : Option V → Option V → Py (Option V)
  | some (.s x), some (.s y) => .ok (some (.s (x ++ y)))
  | some (.s _), y => .error (.typeError s!"can only concatenate str (not \"{tyName y}\") to str")
  | some (.b x ba), some (.b y _) => .ok (some (.b (x ++ y) ba))
  | some (.b _ ba), y => .error (.typeError s!"can't concat {tyName y} to {bytesTy ba}")
  | none, y => .error (.typeError s!"unsupported operand type(s) for +: 'NoneType' and '{tyName y}'")

def hexDigit (n : Nat) : Nat := if n < 10 then 48 + n else 87 + n

/-- `repr(bytes)`, `PyBytes_Repr` (Objects/bytesobject.c), without the `b`. -/
def bytesReprBody (x : Str) : Str :=
  let q := if x.contains 39 && !x.contains 34 then 34 else 39
  q :: x.flatMap (fun c =>
    if c == q || c == 92 then [92, c]
    else if c == 9 then [92, 116] else if c == 10 then [92, 110] else if c == 13 then [92, 114]
    else if c < 32 || c ≥ 127 then [92, 120, hexDigit (c / 16), hexDigit (c % 16)]
    else [c]) ++ [q]

/-- `"%s" % x`. -/
def pyStr : Option V → Str
  | none => cs "None"
  | some (.s x) => x
  | some (.b x false) => 98 :: bytesReprBody x
  | some (.b x true) => cs "bytearray(b" ++ bytesReprBody x ++ [41]

/-- `x[:2] == '//'`. -/
def sliceIsSlashes : Option V → Py Bool
  | none => .error (.typeError "'NoneType' object is not subscriptable")
  | some (.s x) => .ok (x.take 2 == [47, 47])
  | some (.b _ _) => .ok false

/-- `x[:1] == '/'` on a true value. -/
def startsSlash : Option V → Bool
  | some (.s x) => x.take 1 == [47]
  | _ => false

/-! ## Codecs -/

/-- An `encoding` argument. -/
inductive Enc where
  | utf8 | ascii | latin1
  deriving Repr, DecidableEq, Inhabited

def noNames : Nat → Option Str := fun _ => none

/-- `s.encode(encoding, errors)`. -/
def encodeWith : Enc → UnicodeObj.ErrHandler → Str → Py Str
  | .utf8, h, s => UnicodeObj.utf8Encode s h
  | .ascii, h, s => UnicodeObj.ucs1Encode s 128 h noNames
  | .latin1, h, s => UnicodeObj.ucs1Encode s 256 h noNames

/-- `b.decode(encoding, errors)`. -/
def decodeWith : Enc → UnicodeObj.ErrHandler → Str → Py Str
  | .utf8, h, b => UnicodeObj.utf8Decode b h
  | .ascii, h, b => UnicodeObj.asciiDecode b h
  | .latin1, _, b => .ok (UnicodeObj.latin1Decode b)

/-- `s.encode('ascii', 'strict')`. -/
def asciiEnc (s : Str) : Py Str := UnicodeObj.ucs1Encode s 128 .strict noNames

/-! ## List helpers with Python's semantics -/

/-- `s.partition(c)` for one character: the part before, and the part after if `c` occurs. -/
def part (c : Nat) : Str → Str × Option Str
  | [] => ([], none)
  | x :: r =>
    if x == c then ([], some r)
    else
      let p := part c r
      (x :: p.1, p.2)

/-- `s.rpartition(c)`: the part before the last `c` if it occurs, and the part after it. -/
def rpart (c : Nat) (s : Str) : Option Str × Str :=
  match part c s.reverse with
  | (a, none) => (none, a.reverse)
  | (a, some b) => (some b.reverse, a.reverse)

/-- `s.split(sep)` for a non-empty `sep`. -/
def splitOn (sep : Str) : Str → List Str
  | [] => [[]]
  | c :: r =>
    if sep ≠ [] ∧ sep.isPrefixOf (c :: r) then [] :: splitOn sep (r.drop (sep.length - 1))
    else
      match splitOn sep r with
      | [] => [[c]]
      | h :: t => (c :: h) :: t
termination_by s => s.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- `s.count(sep)` for a non-empty `sep`: non-overlapping occurrences. -/
def countSub (sep : Str) (s : Str) : Nat := (splitOn sep s).length - 1

/-- `s.rstrip(chars)` where `chars` is the predicate. -/
def rstripBy (p : Nat → Bool) (s : Str) : Str := (s.reverse.dropWhile p).reverse

/-- `''.join` with a separator: `sep.join(parts)`. -/
def joinWith (sep : Str) : List Str → Str
  | [] => []
  | [x] => x
  | x :: r => x ++ sep ++ joinWith sep r

def isAsciiDigit (c : Nat) : Bool := decide (48 ≤ c) && decide (c ≤ 57)
def isAsciiAlpha (c : Nat) : Bool :=
  (decide (65 ≤ c) && decide (c ≤ 90)) || (decide (97 ≤ c) && decide (c ≤ 122))
def isHex (c : Nat) : Bool :=
  isAsciiDigit c || (decide (65 ≤ c) && decide (c ≤ 70)) || (decide (97 ≤ c) && decide (c ≤ 102))
def hexVal (c : Nat) : Nat := if c ≤ 57 then c - 48 else if c ≤ 70 then c - 55 else c - 87

/-- `int(s)` for a non-empty string of ASCII digits, with the 4300-digit limit of
`sys.int_info.default_max_str_digits` (Objects/longobject.c). -/
def digitsVal (s : Str) : Nat := s.foldl (fun a c => a * 10 + (c - 48)) 0

def intOfDigits (s : Str) : Py Nat :=
  if s.length > 4300 then
    .error (.valueError s!"Exceeds the limit (4300 digits) for integer string conversion: value has {s.length} digits; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (digitsVal s)

/-! ## `_coerce_args`, Lib/urllib/parse.py:113-141 -/

/-- The first `for` of `_coerce_args`, :127-133. -/
def mixLoop : Option Bool → List Arg → Py (Option Bool)
  | si, [] => .ok si
  | si, a :: r =>
    if a.truthy then
      match si with
      | none => mixLoop (some a.isStr) r
      | some b =>
        if a.isStr != b then .error (.typeError "Cannot mix str and non-str arguments")
        else mixLoop si r
    else mixLoop si r

/-- The second `for`, :134-138. -/
def firstNotNone : List Arg → Option Bool
  | [] => none
  | .none :: r => firstNotNone r
  | a :: _ => some a.isStr

/-- An argument left as it is (`args + (_noop,)`). -/
def Arg.toV : Arg → Option V
  | .none => Option.none
  | .str s => some (.s s)
  | .bytes b ba => some (.b b ba)

/-- `_decode_args`, :113-118: `x.decode('ascii', 'strict') if x else '' if x is not None else None`. -/
def decodeArg (x : Arg) : Py (Option V) :=
  if x.truthy then
    match x with
    | .bytes b _ => (UnicodeObj.asciiDecode b .strict).map (fun s => some (.s s))
    | _ => .error (.named "AttributeError" "'str' object has no attribute 'decode'")
  else match x with
    | .none => .ok none
    | _ => .ok (some (.s []))

def decodeArgs : List Arg → Py (List (Option V))
  | [] => .ok []
  | x :: r => do
    let v ← decodeArg x
    let t ← decodeArgs r
    pure (v :: t)

/-- `_coerce_args`: the values, and `true` when the result is to be encoded (`_encode_result`). -/
def coerceArgs (args : List Arg) : Py (List (Option V) × Bool) := do
  let si ← mixLoop none args
  let si := match si with
    | none => firstNotNone args
    | some b => some b
  if si != some false then pure (args.map Arg.toV, false)
  else
    let vs ← decodeArgs args
    pure (vs, true)

/-- `_noop`, or `_encode_result` on a string (:106-111). -/
def coerceStr (isB : Bool) (v : Option V) : Py Arg :=
  match v with
  | some (.s x) => if isB then (asciiEnc x).map (fun y => .bytes y false) else .ok (.str x)
  | some (.b x ba) => .ok (.bytes x ba)
  | none => .ok .none

/-! ## Result objects -/

/-- A `DefragResult`, `SplitResult` or `ParseResult` (or their `Bytes` twins). -/
structure Res where
  fields : List (Option Str)
  isBytes : Bool
  /-- The `_keep_empty` slot: `none` when it is unset. -/
  keep : Option Bool
  deriving Repr, DecidableEq, Inhabited

/-- `_encode_result` on a result object: `_ResultMixinStr.encode('ascii', 'strict')`. -/
def encodeFields : List (Option Str) → Py (List (Option Str))
  | [] => .ok []
  | f :: r => do
    let x ← match f with
      | none => pure none
      | some s => (asciiEnc s).map some
    let t ← encodeFields r
    pure (x :: t)

/-- Build the result and apply `_coerce_result`, then set `_keep_empty`. -/
def mkRes (isB : Bool) (fields : List (Option Str)) (keep : Bool) : Py Res := do
  let f ← if isB then encodeFields fields else pure fields
  pure { fields := f, isBytes := isB, keep := some keep }

/-- The tuple as `urlunsplit` and `urlunparse` see it. -/
structure Comp where
  parts : List Arg
  /-- `getattr(components, '_keep_empty', default)`: `none` when there is no such attribute. -/
  keep : Option Bool
  deriving Repr, DecidableEq, Inhabited

def Res.toComp (r : Res) : Comp :=
  { parts := r.fields.map (fun f => match f with
      | none => .none
      | some x => if r.isBytes then .bytes x false else .str x),
    keep := r.keep }

/-! ## `urlsplit`, Lib/urllib/parse.py:509-625 -/

/-- `_WHATWG_C0_CONTROL_OR_SPACE`, :89: the characters `\x00` to `' '`. -/
def isC0Space (c : Nat) : Bool := decide (c ≤ 32)

/-- The `for b in _UNSAFE_URL_BYTES_TO_REMOVE: url = url.replace(b, "")` loop, :597-598. -/
def removeUnsafe (s : Str) : Str := ((s.filter (· != 9)).filter (· != 13)).filter (· != 10)

def lstripC0 (s : Str) : Str := s.dropWhile isC0Space
def stripC0 (s : Str) : Str := rstripBy isC0Space (s.dropWhile isC0Space)

/-- `scheme_chars`, :82-85. -/
def isSchemeChar (c : Nat) : Bool :=
  isAsciiAlpha c || isAsciiDigit c || c == 43 || c == 45 || c == 46

/-- `_splitnetloc`, :501-507. -/
def splitnetloc (url : Str) (start : Nat) : Str × Str :=
  let findFrom (c : Nat) : Option Nat := ((url.drop start).findIdx? (· == c)).map (· + start)
  let delim := [47, 63, 35].foldl
    (fun d c => match findFrom c with
      | some w => min d w
      | none => d) url.length
  ((url.take delim).drop start, url.drop delim)

/-- The regular expression `\A[vV][a-fA-F0-9]+\..+\z` of :548 (`.` does not match a newline). -/
def ipvFutureOk : Str → Bool
  | c :: r =>
    (c == 118 || c == 86) &&
      let hex := r.takeWhile isHex
      match r.dropWhile isHex with
      | 46 :: t => !hex.isEmpty && !t.isEmpty && t.all (· != 10)
      | _ => false
  | [] => false

/-- `_check_bracketed_host`, :546-553. -/
def checkBracketedHost (ipk : Str → Option Bool) (h : Str) : Py Unit :=
  if h.take 1 == [118] || h.take 1 == [86] then
    if ipvFutureOk h then .ok () else .error (.valueError "IPvFuture address is invalid")
  else
    match ipk h with
    | none => .error (.valueError "~does not appear to be an IPv4 or IPv6 address")
    | some true => .error (.valueError "An IPv4 address cannot be in brackets")
    | some false => .ok ()

/-- `_check_bracketed_netloc`, :527-542. -/
def checkBracketedNetloc (ipk : Str → Option Bool) (netloc : Str) : Py Unit :=
  let hp := (rpart 64 netloc).2
  match part 91 hp with
  | (before, some bracketed) =>
    if !before.isEmpty then .error (.valueError "Invalid IPv6 URL")
    else
      let (hostname, port) := part 93 bracketed
      let port := port.getD []
      if !port.isEmpty && port.take 1 != [58] then .error (.valueError "Invalid IPv6 URL")
      else checkBracketedHost ipk hostname
  | (_, none) => checkBracketedHost ipk (part 58 hp).1

/-- `_checknetloc`, :509-525. -/
def checknetloc (nfkc : Str → Str) (netloc : Option Str) : Py Unit :=
  match netloc with
  | none => .ok ()
  | some n =>
    if n.isEmpty || n.all (· < 128) then .ok ()
    else
      let m := (((n.filter (· != 64)).filter (· != 58)).filter (· != 35)).filter (· != 63)
      let m2 := nfkc m
      if m == m2 then .ok ()
      else if [47, 63, 35, 64, 58].any (fun c => m2.contains c) then
        let msg := if n.any (fun c => decide (0xD800 ≤ c) && decide (c ≤ 0xDFFF)) then "~netloc"
          else "netloc '" ++ toS n ++ "' contains invalid characters under NFKC normalization"
        .error (.valueError msg)
      else .ok ()

/-- The components of `_urlsplit`: scheme, netloc, path, query, fragment. -/
abbrev Split := Option Str × Option Str × Str × Option Str × Option Str

/-- `_urlsplit`, :593-625. `url` is never `None` here. -/
def urlsplitCore (nfkc : Str → Str) (ipk : Str → Option Bool) (url : V) (scheme : Option V)
    (allowFrag : Bool) : Py Split := do
  let url ← match url with
    | .s u => pure (removeUnsafe (lstripC0 u))
    | .b _ _ => throw (.typeError "a bytes-like object is required, not 'str'")
  let scheme ← match scheme with
    | none => pure none
    | some (.s x) => pure (some (removeUnsafe (stripC0 x)))
    | some (.b _ _) => throw (.typeError "a bytes-like object is required, not 'str'")
  let (scheme, url) ← match url.findIdx? (· == 58) with
    | some i =>
      if i > 0 && isAsciiAlpha (url.headD 0) && (url.take i).all isSchemeChar then do
        let l ← UnicodeObj.unicodeLower (url.take i)
        pure (some l, url.drop (i + 1))
      else pure (scheme, url)
    | none => pure (scheme, url)
  let (netloc, url) ← if url.take 2 == [47, 47] then do
      let (n, rest) := splitnetloc url 2
      if (n.contains 91 && !n.contains 93) || (n.contains 93 && !n.contains 91) then
        throw (.valueError "Invalid IPv6 URL")
      if n.contains 91 && n.contains 93 then checkBracketedNetloc ipk n
      pure (some n, rest)
    else pure (none, url)
  let (url, fragment) := if allowFrag && url.contains 35 then part 35 url else (url, none)
  let (url, query) := if url.contains 63 then part 63 url else (url, none)
  checknetloc nfkc netloc
  pure (scheme, netloc, url, query, fragment)

/-- The `functools.lru_cache` of `urlsplit` hashes its arguments, :557. -/
def lruHash (args : List Arg) : Py Unit :=
  if args.any (fun a => match a with
    | .bytes _ true => true
    | _ => false) then .error (.typeError "unhashable type: 'bytearray'")
  else .ok ()

def fillMissing (missingAsNone : Bool) (x : Option Str) : Option Str :=
  if missingAsNone then x else some (x.getD [])

/-- `urlsplit`, :557-591. -/
def urlsplit (nfkc : Str → Str) (ipk : Str → Option Bool) (url scheme : Arg) (allowFrag : Bool)
    (missingAsNone : Bool) : Py Res := do
  lruHash [url, scheme]
  let (vs, isB) ← coerceArgs [url, scheme]
  let u := (vs.headD none).getD (.s [])
  let sc := vs.getD 1 none
  let (scheme, netloc, path, query, fragment) ← urlsplitCore nfkc ipk u sc allowFrag
  let f := fillMissing missingAsNone
  mkRes isB [f scheme, f netloc, some path, f query, f fragment] missingAsNone

/-- `_splitparams(url, missing_as_none=True)`, :492-499, as `_urlparse` calls it. -/
def splitparams (url : Str) : Str × Option Str :=
  if url.contains 47 then
    let r := (rpart 47 url).1.map (·.length) |>.getD 0
    match (url.drop r).findIdx? (· == 59) with
    | none => (url, none)
    | some j => (url.take (r + j), some (url.drop (r + j + 1)))
  else
    match url.findIdx? (· == 59) with
    | some i => (url.take i, some (url.drop (i + 1)))
    | none => (url.take (url.length - 1), some url)

/-- `uses_params`, :64-66. -/
def usesParams : List Str :=
  ["", "ftp", "hdl", "prospero", "http", "imap", "https", "shttp", "rtsp", "rtsps", "rtspu", "sip",
   "sips", "mms", "sftp", "tel"].map cs

/-- `uses_netloc`, :58-62. -/
def usesNetloc : List Str :=
  ["", "ftp", "http", "gopher", "nntp", "telnet", "imap", "wais", "file", "mms", "https", "shttp",
   "snews", "prospero", "rtsp", "rtsps", "rtspu", "rsync", "svn", "svn+ssh", "sftp", "nfs", "git",
   "git+ssh", "ws", "wss", "itms-services"].map cs

/-- `uses_relative`, :53-56. -/
def usesRelative : List Str :=
  ["", "ftp", "http", "gopher", "nntp", "imap", "wais", "file", "https", "shttp", "mms", "prospero",
   "rtsp", "rtsps", "rtspu", "sftp", "svn", "svn+ssh", "ws", "wss"].map cs

/-- `_urlparse`, :484-490. -/
def urlparseCore (nfkc : Str → Str) (ipk : Str → Option Bool) (url : V) (scheme : Option V)
    (allowFrag : Bool) : Py (Option Str × Option Str × Str × Option Str × Option Str × Option Str) := do
  let (scheme, netloc, url, query, fragment) ← urlsplitCore nfkc ipk url scheme allowFrag
  let (url, params) := if usesParams.contains (scheme.getD []) && url.contains 59 then splitparams url
    else (url, none)
  pure (scheme, netloc, url, params, query, fragment)

/-- `urlparse`, :447-482 (no cache). -/
def urlparse (nfkc : Str → Str) (ipk : Str → Option Bool) (url scheme : Arg) (allowFrag : Bool)
    (missingAsNone : Bool) : Py Res := do
  let (vs, isB) ← coerceArgs [url, scheme]
  let u := (vs.headD none).getD (.s [])
  let sc := vs.getD 1 none
  let (scheme, netloc, path, params, query, fragment) ← urlparseCore nfkc ipk u sc allowFrag
  let f := fillMissing missingAsNone
  mkRes isB [f scheme, f netloc, some path, f params, f query, f fragment] missingAsNone

/-! ## `urlunsplit` and `urlunparse`, :627-695 -/

/-- `_urlunsplit`, :683-695. -/
def urlunsplitCore (scheme netloc url query fragment : Option V) : Py (Option V) := do
  let url ← if netloc.isSome then do
      let url ← if truthy url && !startsSlash url then add (some (.s [47])) url else pure url
      let t ← add (some (.s [47, 47])) netloc
      add t url
    else do
      if ← sliceIsSlashes url then add (some (.s [47, 47])) url else pure url
  let url ← if truthy scheme then do
      let t ← add scheme (some (.s [58]))
      add t url
    else pure url
  let url ← if query.isSome then do
      let t ← add url (some (.s [63]))
      add t query
    else pure url
  if fragment.isSome then do
    let t ← add url (some (.s [35]))
    add t fragment
  else pure url

def unpackErr (expected got : Nat) : PyExc :=
  if got < expected then .valueError s!"not enough values to unpack (expected {expected}, got {got})"
  else .valueError s!"too many values to unpack (expected {expected}, got {got})"

/-- `x in uses_netloc` for a value. -/
def inList (l : List Str) : Option V → Bool
  | some (.s x) => l.contains x
  | _ => false

/-- The `keep_empty` handling of :636-641 and :666-671. -/
def keepOf (c : Comp) (keepEmpty : Option Bool) : Py Bool :=
  match keepEmpty with
  | none => .ok (c.keep.getD false)
  | some k =>
    if k && !(c.keep.getD true) then
      .error (.valueError "Cannot distinguish between empty and not defined URI components in the result of parsing URL with missing_as_none=False")
    else .ok k

/-- `netloc` when it is false and `keep_empty` is false, :643-647 and :673-677. -/
def fixNetloc (scheme netloc url : Option V) : Option V :=
  if !truthy netloc then
    if truthy scheme && inList usesNetloc scheme && (!truthy url || startsSlash url) then some (.s [])
    else none
  else netloc

def noneIfFalse (x : Option V) : Option V := if truthy x then x else none

/-- `urlunsplit`, :656-681. -/
def urlunsplit (c : Comp) (keepEmpty : Option Bool) : Py Arg := do
  let (vs, isB) ← coerceArgs c.parts
  match vs with
  | [scheme, netloc, url, query, fragment] =>
    let keep ← keepOf c keepEmpty
    let (scheme, netloc, query, fragment) := if !keep then
        (noneIfFalse scheme, fixNetloc scheme netloc url, noneIfFalse query, noneIfFalse fragment)
      else (scheme, netloc, query, fragment)
    let r ← urlunsplitCore scheme netloc url query fragment
    coerceStr isB r
  | _ => throw (unpackErr 6 (vs.length + 1))

/-- `urlunparse`, :627-654. -/
def urlunparse (c : Comp) (keepEmpty : Option Bool) : Py Arg := do
  let (vs, isB) ← coerceArgs c.parts
  match vs with
  | [scheme, netloc, url, params, query, fragment] =>
    let keep ← keepOf c keepEmpty
    let (scheme, netloc, params, query, fragment) := if !keep then
        (noneIfFalse scheme, fixNetloc scheme netloc url, noneIfFalse params, noneIfFalse query,
          noneIfFalse fragment)
      else (scheme, netloc, params, query, fragment)
    let url := if params.isSome then some (.s (pyStr url ++ [59] ++ pyStr params)) else url
    let r ← urlunsplitCore scheme netloc url query fragment
    coerceStr isB r
  | _ => throw (unpackErr 7 (vs.length + 1))

/-- `SplitResult.geturl`, :334-335, and `ParseResult.geturl`, :341-342. -/
def splitGeturl (r : Res) : Py Arg := urlunsplit r.toComp none
def parseGeturl (r : Res) : Py Arg := urlunparse r.toComp none

/-! ## `urldefrag` and `DefragResult.geturl`, :323-328 and :769-786 -/

def urldefrag (nfkc : Str → Str) (ipk : Str → Option Bool) (url : Arg) (missingAsNone : Bool) :
    Py Res := do
  let (vs, isB) ← coerceArgs [url]
  let u ← match vs.headD none with
    | none => throw (.typeError "argument of type 'NoneType' is not a container or iterable")
    | some (.b _ _) => throw (.typeError "a bytes-like object is required, not 'str'")
    | some (.s x) => pure x
  let (defrag, frag) ← if u.contains 35 then do
      let (s, n, p, q, frag) ← urlsplitCore nfkc ipk (.s u) none true
      let d ← urlunsplitCore (s.map .s) (n.map .s) (some (.s p)) (q.map .s) none
      pure (d, frag)
    else pure (some (.s u), none)
  let frag := if !missingAsNone && frag.isNone then some [] else frag
  let d := match defrag with
    | some (.s x) => x
    | _ => []
  mkRes isB [some d, frag] missingAsNone

/-- `_DefragResultBase.geturl`, :323-328. -/
def defragGeturl (r : Res) : Py Arg :=
  match r.fields with
  | [url, fragment] =>
    let wrap (x : Option Str) : Option V := x.map (fun y => if r.isBytes then .b y false else .s y)
    let hash : Option V := some (if r.isBytes then .b [35] false else .s [35])
    let keep := r.keep.getD false
    let fr := wrap fragment
    if truthy fr || (fragment.isSome && keep) then do
      let t ← add (wrap url) hash
      let x ← add t fr
      coerceStr false x
    else coerceStr false (wrap url)
  | _ => .error .modelFuel

/-! ## `urljoin`, :697-766 -/

/-- `segments[1:-1] = filter(None, segments[1:-1])`. -/
def filterMid (l : List Str) : List Str :=
  match l with
  | a :: b :: r =>
    let mid := (b :: r).dropLast
    a :: mid.filter (fun x => !x.isEmpty) ++ [(b :: r).getLast (by simp)]
  | _ => l

/-- The `for seg in segments` loop, :747-758. -/
def resolveSegs : List Str → List Str → List Str
  | acc, [] => acc
  | acc, seg :: r =>
    if seg == cs ".." then resolveSegs acc.dropLast r
    else if seg == cs "." then resolveSegs acc r
    else resolveSegs (acc ++ [seg]) r

/-- The path resolution of :730-766. -/
def resolvePath (bpath path : Str) : Str :=
  let baseParts := splitOn [47] bpath
  let baseParts := if baseParts.getLast? != some [] then baseParts.dropLast else baseParts
  let segments := if path.take 1 == [47] then splitOn [47] path
    else filterMid (baseParts ++ splitOn [47] path)
  let resolved := resolveSegs [] segments
  let resolved := if segments.getLast? == some (cs ".") || segments.getLast? == some (cs "..") then
      resolved ++ [[]] else resolved
  let j := joinWith [47] resolved
  if j.isEmpty then [47] else j

def lift (x : Option Str) : Option V := x.map .s

/-- `urljoin`, :697-766. -/
def urljoin (nfkc : Str → Str) (ipk : Str → Option Bool) (base url : Arg) (allowFrag : Bool) :
    Py Arg := do
  if !base.truthy then return url
  if !url.truthy then return base
  let (vs, isB) ← coerceArgs [base, url]
  let b := (vs.headD none).getD (.s [])
  let u := (vs.getD 1 none).getD (.s [])
  let (bscheme, bnetloc, bpath, bquery, bfragment) ← urlsplitCore nfkc ipk b none allowFrag
  let (scheme, netloc, path, query, fragment) ← urlsplitCore nfkc ipk u none allowFrag
  let scheme := if scheme.isNone then bscheme else scheme
  if scheme != bscheme || (!(scheme.getD []).isEmpty && !usesRelative.contains (scheme.getD [])) then
    return ← coerceStr isB (some u)
  let netloc ← if (scheme.getD []).isEmpty || usesNetloc.contains (scheme.getD []) then
      if !(netloc.getD []).isEmpty then do
        let r ← urlunsplitCore (lift scheme) (lift netloc) (some (.s path)) (lift query) (lift fragment)
        return ← coerceStr isB r
      else pure bnetloc
    else pure netloc
  if path.isEmpty then
    let query' := if query.isNone then bquery else query
    let fragment' := if query.isNone && fragment.isNone then bfragment else fragment
    let r ← urlunsplitCore (lift scheme) (lift netloc) (some (.s bpath)) (lift query') (lift fragment')
    return ← coerceStr isB r
  let r ← urlunsplitCore (lift scheme) (lift netloc) (some (.s (resolvePath bpath path))) (lift query)
    (lift fragment)
  coerceStr isB r

/-! ## Unquoting, :788-990 -/

/-- The `for item in bits[1:]` loop of `_unquote_impl`, :815-821. -/
def unquoteItems : List Str → Str
  | [] => []
  | item :: r =>
    match item with
    | h1 :: h2 :: t =>
      if isHex h1 && isHex h2 then (hexVal h1 * 16 + hexVal h2) :: t ++ unquoteItems r
      else 37 :: item ++ unquoteItems r
    | _ => 37 :: item ++ unquoteItems r

/-- `_unquote_impl`, :795-822, returning the bytes. -/
def unquoteImpl (s : Arg) : Py Str := do
  if !s.truthy then
    match s with
    | .none => throw (.named "AttributeError" "'NoneType' object has no attribute 'split'")
    | _ => return []
  let b ← match s with
    | .str x => UnicodeObj.utf8Encode x .strict
    | .bytes x _ => pure x
    | .none => pure []
  let bits := splitOn [37] b
  match bits with
  | [_] => pure b
  | first :: items =>
    match s with
    | .bytes _ true =>
      throw (.typeError "cannot use 'bytearray' as a dict key (unhashable type: 'bytearray')")
    | _ => pure (first ++ unquoteItems items)
  | [] => pure b

/-- `unquote_to_bytes`, :791-793. -/
def unquoteToBytes (s : Arg) : Py Str := unquoteImpl s

/-- `''.join(_generate_unquoted_parts(string, encoding, errors))`, :826-834: runs of ASCII
characters are unquoted and decoded, the rest is kept. -/
def genParts (enc : Enc) (h : UnicodeObj.ErrHandler) : Nat → Str → Py Str
  | 0, _ => .error .modelFuel
  | fuel + 1, s =>
    let gap := s.takeWhile (· ≥ 128)
    let rest := s.dropWhile (· ≥ 128)
    if rest.isEmpty then .ok gap
    else do
      let run := rest.takeWhile (· < 128)
      let d ← decodeWith enc h (← unquoteImpl (.str run))
      let t ← genParts enc h fuel (rest.dropWhile (· < 128))
      pure (gap ++ d ++ t)

/-- `unquote`, :836-856. `none` is an explicit `None`. -/
def unquote (string : Arg) (encoding : Option Enc) (errors : Option UnicodeObj.ErrHandler) :
    Py Str :=
  match string with
  | .bytes x false => do
    let b ← unquoteImpl (.bytes x false)
    match encoding, errors with
    | none, _ => throw (.typeError "decode() argument 'encoding' must be str, not None")
    | _, none => throw (.typeError "decode() argument 'errors' must be str, not None")
    | some e, some h => decodeWith e h b
  | .bytes _ true => .error (.typeError "a bytes-like object is required, not 'str'")
  | .none => .error (.typeError "argument of type 'NoneType' is not a container or iterable")
  | .str x =>
    if !x.contains 37 then .ok x
    else genParts (encoding.getD .utf8) (errors.getD .replace) (x.length + 1) x

/-- `unquote_plus`, :983-990. -/
def unquotePlus (string : Arg) (encoding : Option Enc) (errors : Option UnicodeObj.ErrHandler) :
    Py Str :=
  match string with
  | .str x => unquote (.str (x.map (fun c => if c == 43 then 32 else c))) encoding errors
  | .bytes _ _ => .error (.typeError "a bytes-like object is required, not 'str'")
  | .none => .error (.named "AttributeError" "'NoneType' object has no attribute 'replace'")

/-! ## Quoting, :992-1121 -/

/-- `_ALWAYS_SAFE`, :992-995. -/
def alwaysSafe (c : Nat) : Bool :=
  isAsciiAlpha c || isAsciiDigit c || c == 95 || c == 46 || c == 45 || c == 126

def hexU (n : Nat) : Nat := if n < 10 then 48 + n else 55 + n

/-- `_Quoter.__init__` (:1007-1009) builds `_ALWAYS_SAFE.union(safe)`, and `_Quoter.__missing__`
(:1014-1018) maps a byte to `chr(b)` or `'%{:02X}'`. The dict only caches `__missing__`. -/
def quoteByte (safe : Str) (b : Nat) : Str :=
  if alwaysSafe b || safe.contains b then [b] else [37, hexU (b / 16), hexU (b % 16)]

/-- `[bs[i:i+n] for i in range(0, len(bs), n)]` for `n > 0`. -/
def chunks (n : Nat) (l : Str) : List Str :=
  if h : n = 0 ∨ l = [] then [l]
  else l.take n :: (if l.length ≤ n then [] else chunks n (l.drop n))
termination_by l.length
decreasing_by simp_wf; omega

/-- `quote_from_bytes` once `safe` is normalized, :1111-1121: the fast path, the path below
200,000 bytes, and the chunked path. -/
def quoteTail (x safe : Str) : Py Str :=
  if (rstripBy (fun c => alwaysSafe c || safe.contains c) x).isEmpty then
    UnicodeObj.utf8Decode x .strict
  else if x.length < 200000 then .ok (x.flatMap (quoteByte safe))
  else .ok ((chunks (Nat.sqrt x.length) x).flatMap (fun c => c.flatMap (quoteByte safe)))

/-- `safe` normalized: `safe.encode('ascii', 'ignore')` or `bytes([c for c in safe if c < 128])`. -/
def normSafe : Arg → Py Str
  | .str s => UnicodeObj.ucs1Encode s 128 .ignore noNames
  | .bytes s _ => .ok (s.filter (· < 128))
  | .none => .error (.typeError "'NoneType' object is not iterable")

/-- `quote_from_bytes`, :1096-1121. `safe` is a `str` or `bytes`. -/
def quoteFromBytes (bs safe : Arg) : Py Str := do
  let x ← match bs with
    | .bytes x _ => pure x
    | _ => throw (.typeError "quote_from_bytes() expected bytes")
  if x.isEmpty then return []
  let safe ← normSafe safe
  quoteTail x safe

/-- `quote`, :1020-1072. `encoding`/`errors` are `none` for `None`. -/
def quote (string safe : Arg) (encoding : Option Enc) (errors : Option UnicodeObj.ErrHandler) :
    Py Str :=
  match string with
  | .str s =>
    if s.isEmpty then .ok s
    else do
      let b ← encodeWith (encoding.getD .utf8) (errors.getD .strict) s
      quoteFromBytes (.bytes b false) safe
  | other =>
    if encoding.isSome then .error (.typeError "quote() doesn't support 'encoding' for bytes")
    else if errors.isSome then .error (.typeError "quote() doesn't support 'errors' for bytes")
    else quoteFromBytes other safe

/-- `safe + space`, :1084-1088: `' '` for a `str`, `b' '` otherwise. -/
def addSpace : Arg → Py Arg
  | .str s => .ok (.str (s ++ [32]))
  | .bytes b ba => .ok (.bytes (b ++ [32]) ba)
  | .none => .error (.typeError "unsupported operand type(s) for +: 'NoneType' and 'bytes'")

/-- `quote_plus`, :1074-1089. -/
def quotePlus (string safe : Arg) (encoding : Option Enc) (errors : Option UnicodeObj.ErrHandler) :
    Py Str := do
  let noSpace := match string with
    | .str s => !s.contains 32
    | .bytes b false => !b.contains 32
    | _ => false
  if noSpace then return ← quote string safe encoding errors
  let safe2 ← addSpace safe
  let r ← quote string safe2 encoding errors
  pure (r.map (fun c => if c == 32 then 43 else c))

/-! ## Query strings, :859-981 and :1123-1200 -/

/-- The options of `parse_qsl`. `encoding`/`errors` are `none` for `None`. -/
structure QslOpts where
  keepBlank : Bool := false
  strict : Bool := false
  encoding : Option Enc := some .utf8
  errors : Option UnicodeObj.ErrHandler := some .replace
  maxNum : Option Int := none
  sep : Arg := .str [38]
  deriving Repr, Inhabited

/-- The `for name_value in qs.split(separator)` loop, :971-980. -/
def qslLoop (o : QslOpts) (unq : Str → Py Str) : List Str → Py (List (Str × Str))
  | [] => .ok []
  | nv :: r => do
    let here ← if !nv.isEmpty || o.strict then
        let (name, value) := part 61 nv
        if value.isNone && o.strict then
          throw (.valueError "~bad query field")
        else
          let value := value.getD []
          if !value.isEmpty || o.keepBlank then do
            let n ← unq name
            let v ← unq value
            pure [(n, v)]
          else pure []
      else pure []
    let t ← qslLoop o unq r
    pure (here ++ t)

/-- `parse_qsl`, :902-981: the pairs, and whether they are `bytes`. -/
def parseQsl (qs : Arg) (o : QslOpts) : Py (List (Str × Str)) := do
  let sepOk := match o.sep with
    | .str s => !s.isEmpty
    | .bytes b false => !b.isEmpty
    | _ => false
  if !sepOk then throw (.valueError "Separator must be of type string or bytes.")
  let (q, sep, unq) ← match qs with
    | .str q => do
      let sep ← match o.sep with
        | .bytes b _ => UnicodeObj.asciiDecode b .strict
        | .str s => pure s
        | .none => pure []
      pure (q, sep, fun s => unquotePlus (.str s) o.encoding o.errors)
    | .none => return []
    | .bytes q _ => do
      let sep ← match o.sep with
        | .str s => asciiEnc s
        | .bytes b _ => pure b
        | .none => pure []
      pure (q, sep, fun s => unquoteToBytes (.bytes (s.map (fun c => if c == 43 then 32 else c)) false))
  if q.isEmpty then return []
  if let some m := o.maxNum then
    if m < ((1 + countSub sep q : Nat) : Int) then throw (.valueError "Max number of fields exceeded")
  qslLoop o unq (splitOn sep q)

/-- `parse_qs`, :859-899: the keys in first-seen order, each with its values. -/
def groupPairs : List (Str × Str) → List (Str × List Str) → List (Str × List Str)
  | [], acc => acc
  | (n, v) :: r, acc =>
    if acc.any (·.1 == n) then
      groupPairs r (acc.map (fun p => if p.1 == n then (p.1, p.2 ++ [v]) else p))
    else groupPairs r (acc ++ [(n, [v])])

def parseQs (qs : Arg) (o : QslOpts) : Py (List (Str × List Str)) := do
  let pairs ← parseQsl qs o
  pure (groupPairs pairs [])

/-- A key or value given to `urlencode`. -/
inductive QV where
  | str (s : Str)
  | bytes (b : Str)
  /-- Another object: `str(v)`, and its items when `len(v)` works. -/
  | obj (text : Str) (items : Option (List QV))
  deriving Repr, Inhabited

/-- `str(v)`. -/
def QV.text : QV → Str
  | .str s => s
  | .bytes b => 98 :: bytesReprBody b
  | .obj t _ => t

/-- The `query` argument of `urlencode`. -/
inductive Query where
  /-- An object with `items`. -/
  | mapping (items : List (QV × QV))
  /-- A sequence; each element is a tuple (`true`) or a list, of its items. -/
  | seq (elems : List (Bool × List QV))
  /-- An object without `len`. -/
  | noLen
  deriving Repr, Inhabited

/-- `quote_via`: `quote_plus` (the default) or `quote`. -/
inductive QuoteVia where
  | plus | plain
  deriving Repr, DecidableEq, Inhabited

/-- The options of `urlencode`. -/
structure EncOpts where
  doseq : Bool := false
  safe : Arg := .str []
  encoding : Option Enc := none
  errors : Option UnicodeObj.ErrHandler := none
  via : QuoteVia := .plus
  deriving Repr, Inhabited

def callVia (o : EncOpts) (x : Arg) (withEnc : Bool) : Py Str :=
  let e := if withEnc then o.encoding else none
  let h := if withEnc then o.errors else none
  match o.via with
  | .plus => quotePlus x o.safe e h
  | .plain => quote x o.safe e h

/-- `quote_via(k, safe)` for `bytes`, else `quote_via(str(k), safe, encoding, errors)`. -/
def quoteQV (o : EncOpts) : QV → Py Str
  | .bytes b => callVia o (.bytes b false) false
  | v => callVia o (.str v.text) true

/-- The loops of :1159-1199, over the pairs. -/
def encodeLoop (o : EncOpts) : List (List QV) → Py (List Str)
  | [] => .ok []
  | kv :: r => do
    let (k, v) ← match kv with
      | [k, v] => pure (k, v)
      | l => throw (unpackErr 2 l.length)
    let k ← quoteQV o k
    let here ← if !o.doseq then do
        let v ← quoteQV o v
        pure [k ++ [61] ++ v]
      else
        match v with
        | .obj _ (some items) => items.mapM (fun e => do
            let e ← quoteQV o e
            pure (k ++ [61] ++ e))
        | v => do
          let v ← quoteQV o v
          pure [k ++ [61] ++ v]
    let t ← encodeLoop o r
    pure (here ++ t)

/-- `urlencode`, :1123-1200. -/
def urlencode (query : Query) (o : EncOpts) : Py Str := do
  let pairs ← match query with
    | .mapping items => pure (items.map (fun p => [p.1, p.2]))
    | .seq elems =>
      match elems with
      | (false, _) :: _ => throw (.typeError "not a valid non-string sequence or mapping object")
      | _ => pure (elems.map (·.2))
    | .noLen => throw (.typeError "not a valid non-string sequence or mapping object")
  let l ← encodeLoop o pairs
  pure (joinWith [38] l)

/-! ## The `netloc` attributes, :174-277 -/

/-- `_NetlocResultMixinStr._userinfo`, :215-227. -/
def userinfoS (netloc : Option Str) : Option Str × Option Str :=
  match netloc with
  | none => (none, none)
  | some n =>
    match (rpart 64 n).1 with
    | some userinfo =>
      let (u, p) := part 58 userinfo
      (some u, p)
    | none => (none, none)

/-- `_NetlocResultMixinStr._hostinfo`, :229-243. -/
def hostinfoS (netloc : Option Str) : Option Str × Option Str :=
  match netloc with
  | none => (none, none)
  | some n =>
    let hostinfo := (rpart 64 n).2
    let (hostname, port) := match part 91 hostinfo with
      | (_, some bracketed) =>
        let (h, p) := part 93 bracketed
        (h, ((part 58 (p.getD [])).2).getD [])
      | (_, none) =>
        let (h, p) := part 58 hostinfo
        (h, p.getD [])
    (some hostname, if port.isEmpty then none else some port)

/-- `_NetlocResultMixinBytes._userinfo`, :249-261. -/
def userinfoB (netloc : Option Str) : Option Str × Option Str :=
  match netloc with
  | none => (none, none)
  | some n =>
    match (rpart 64 n).1 with
    | some userinfo =>
      let (u, p) := part 58 userinfo
      (some u, p)
    | none => (none, none)

/-- `_NetlocResultMixinBytes._hostinfo`, :263-277. -/
def hostinfoB (netloc : Option Str) : Option Str × Option Str :=
  match netloc with
  | none => (none, none)
  | some n =>
    let hostinfo := (rpart 64 n).2
    let (hostname, port) := match part 91 hostinfo with
      | (_, some bracketed) =>
        let (h, p) := part 93 bracketed
        (h, ((part 58 (p.getD [])).2).getD [])
      | (_, none) =>
        let (h, p) := part 58 hostinfo
        (h, p.getD [])
    (some hostname, if port.isEmpty then none else some port)

/-- The `netloc` field of a result (index 1). -/
def Res.netloc (r : Res) : Option Str := (r.fields.getD 1 none)

/-- `username` and `password`, :178-184. -/
def username (r : Res) : Option Str :=
  if r.isBytes then (userinfoB r.netloc).1 else (userinfoS r.netloc).1
def password (r : Res) : Option Str :=
  if r.isBytes then (userinfoB r.netloc).2 else (userinfoS r.netloc).2

/-- `hostname`, :186-195: `str.lower` for `str`, `bytes.lower` for `bytes`. -/
def hostname (r : Res) : Py (Option Str) :=
  let hi := if r.isBytes then hostinfoB r.netloc else hostinfoS r.netloc
  match hi.1 with
  | none => .ok none
  | some h =>
    if h.isEmpty then .ok none
    else
      let (a, z) := part 37 h
      let tail := match z with
        | some z => 37 :: z
        | none => []
      if r.isBytes then .ok (some (a.map UnicodeObj.pyToLower ++ tail))
      else (UnicodeObj.unicodeLower a).map (fun l => some (l ++ tail))

/-- `port`, :197-207. -/
def port (r : Res) : Py (Option Nat) :=
  let hi := if r.isBytes then hostinfoB r.netloc else hostinfoS r.netloc
  match hi.2 with
  | none => .ok none
  | some p =>
    if !p.isEmpty && p.all isAsciiDigit then do
      let n ← intOfDigits p
      if n ≤ 65535 then pure (some n) else throw (.valueError "Port out of range 0-65535")
    else .error (.valueError "~Port could not be cast to integer value")

/-- `_ResultMixinStr.encode` (:148-156) and `_ResultMixinBytes.decode` (:163-171). -/
def resEncode (r : Res) (e : Enc) (h : UnicodeObj.ErrHandler) : Py Res := do
  let f ← r.fields.mapM (fun x => match x with
    | none => pure none
    | some s => (encodeWith e h s).map some)
  pure { fields := f, isBytes := true, keep := r.keep }

def resDecode (r : Res) (e : Enc) (h : UnicodeObj.ErrHandler) : Py Res := do
  let f ← r.fields.mapM (fun x => match x with
    | none => pure none
    | some s => (decodeWith e h s).map some)
  pure { fields := f, isBytes := false, keep := r.keep }

/-! ## The legacy helpers, :1209-1407 (`str` arguments) -/

/-- `_to_bytes`, :1209-1220, on a `str`. -/
def toBytes (url : Str) : Py Str :=
  if url.all (· < 128) then .ok url
  else .error (.named "UnicodeError" "~URL contains non-ASCII characters")

/-- `url.strip()`: `Py_UNICODE_ISSPACE`. -/
def stripWs (s : Str) : Str := rstripBy UnicodeObj.isSpace (s.dropWhile UnicodeObj.isSpace)

/-- `unwrap`, :1223-1233, on a `str`. -/
def unwrap (url : Str) : Str :=
  let url := stripWs url
  let url := if url.take 1 == [60] && url.reverse.take 1 == [62] then stripWs ((url.drop 1).dropLast)
    else url
  if url.take 4 == cs "URL:" then stripWs (url.drop 4) else url

/-- `_splittype`, :1244-1254: `re.match('([^/:]+):(.*)', url, re.DOTALL)`. -/
def splittype (url : Str) : Py (Option Str × Str) :=
  let run := url.takeWhile (fun c => c != 47 && c != 58)
  if !run.isEmpty && (url.drop run.length).take 1 == [58] then
    (UnicodeObj.unicodeLower run).map (fun l => (some l, url.drop (run.length + 1)))
  else .ok (none, url)

/-- `_splithost`, :1265-1277: `re.match('//([^/#?]*)(.*)', url, re.DOTALL)`. -/
def splithost (url : Str) : Option Str × Str :=
  if url.take 2 == [47, 47] then
    let r := url.drop 2
    let hp := r.takeWhile (fun c => c != 47 && c != 35 && c != 63)
    let path := r.drop hp.length
    let path := if !path.isEmpty && path.take 1 != [47] then 47 :: path else path
    (some hp, path)
  else (none, url)

/-- `_splituser`, :1287-1290. -/
def splituser (host : Str) : Option Str × Str := rpart 64 host

/-- `_splitpasswd`, :1300-1303. -/
def splitpasswd (user : Str) : Str × Option Str := part 58 user

/-- `_splitport`, :1315-1326: `re.fullmatch('(.*):([0-9]*)', host, re.DOTALL)`. -/
def splitport (host : Str) : Str × Option Str :=
  match rpart 58 host with
  | (some h, p) =>
    if p.all isAsciiDigit then (h, if p.isEmpty then none else some p) else (host, none)
  | (none, _) => (host, none)

/-- `_splitnport`, :1336-1350. -/
def splitnport (host : Str) (defport : Int) : Py (Str × Option Int) :=
  match rpart 58 host with
  | (none, p) => .ok (p, some defport)
  | (some h, p) =>
    if p.isEmpty then .ok (h, some defport)
    else if p.all isAsciiDigit then (intOfDigits p).map (fun n => (h, some (n : Int)))
    else .ok (h, none)

/-- `_splitquery`, :1360-1365, and `_splittag`, :1375-1380. -/
def splitquery (url : Str) : Str × Option Str :=
  match rpart 63 url with
  | (some p, q) => (p, some q)
  | (none, _) => (url, none)

def splittag (url : Str) : Str × Option Str :=
  match rpart 35 url with
  | (some p, q) => (p, some q)
  | (none, _) => (url, none)

/-- `_splitattr`, :1390-1394. -/
def splitattr (url : Str) : Str × List Str :=
  match splitOn [59] url with
  | w :: r => (w, r)
  | [] => ([], [])

/-- `_splitvalue`, :1404-1407. -/
def splitvalue (attr : Str) : Str × Option Str := part 61 attr

end PyLean.TextLibs.Url
