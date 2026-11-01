import PyLean.JsonMod.DecC
import PyLean.JsonMod.Chunks

/-!
The public layer of `json`: `JSONDecodeError`, `JSONDecoder.__init__`,
`detect_encoding`, `loads`, `load` (Lib/json/__init__.py, decoder.py) and
`JSONEncoder.__init__`, `dumps`, `dump` (Lib/json/__init__.py, encoder.py).

`cls=` is out of scope (a subclass can do anything). An unknown keyword argument
reaches `JSONDecoder(**kw)` or `JSONEncoder(**kw)`, which reject it. The codecs
of `bytes.decode` are modelled as far as `json.loads` reaches them, with
`errors='surrogatepass'`.
-/

namespace PyLean.JsonMod

open PyLean

/-! ### `JSONDecodeError`, decoder.py:20-43 -/

structure JDE where
  msg : String
  doc : PStr
  pos : Int
  lineno : Int
  colno : Int
  errmsg : String
  deriving DecidableEq, Repr

/-- `JSONDecodeError.__init__`, decoder.py:31-40. -/
def jdeInit (msg : String) (doc : PStr) (pos : Int) : JDE :=
  let lineno : Int := countNl doc pos + 1
  let colno : Int := pos - rfindNl doc pos
  { msg, doc, pos, lineno, colno
    errmsg := s!"{msg}: line {lineno} column {colno} (char {pos})" }

/-- The arguments of `JSONDecodeError.__reduce__`, decoder.py:42-43. -/
def jdeReduce (e : JDE) : String × PStr × Int := (e.msg, e.doc, e.pos)

/-! ### `bytes.decode(encoding, 'surrogatepass')` -/

/-- `UnicodeDecodeError`: the message embeds bytes and positions. -/
def decErr : PyExc := .named "UnicodeDecodeError" "~invalid data"

def isCont (b : Nat) : Bool := 0x80 ≤ b && b ≤ 0xbf

/-- One UTF-8 sequence: the code point and the length. `surrogatepass` admits
the three-byte forms of surrogates. -/
def utf8Seq : List Nat → Option (Nat × Nat)
  | [] => none
  | a :: r =>
    if a < 0x80 then some (a, 1)
    else if 0xc2 ≤ a ∧ a ≤ 0xdf then
      match r with
      | b :: _ => if isCont b then some ((a - 0xc0) * 64 + (b - 0x80), 2) else none
      | _ => none
    else if 0xe0 ≤ a ∧ a ≤ 0xef then
      match r with
      | b :: c :: _ =>
        if isCont b ∧ isCont c ∧ (a = 0xe0 → 0xa0 ≤ b) then
          some ((a - 0xe0) * 4096 + (b - 0x80) * 64 + (c - 0x80), 3)
        else none
      | _ => none
    else if 0xf0 ≤ a ∧ a ≤ 0xf4 then
      match r with
      | b :: c :: d :: _ =>
        if isCont b ∧ isCont c ∧ isCont d ∧ (a = 0xf0 → 0x90 ≤ b) ∧ (a = 0xf4 → b ≤ 0x8f) then
          some ((a - 0xf0) * 262144 + (b - 0x80) * 4096 + (c - 0x80) * 64 + (d - 0x80), 4)
        else none
      | _ => none
    else none

def utf8Dec : Nat → List Nat → Except PyExc PStr
  | 0, _ => .error .modelFuel
  | _ + 1, [] => .ok []
  | f + 1, b =>
    match utf8Seq b with
    | none => .error decErr
    | some (c, n) => (utf8Dec f (b.drop n)).map (c :: ·)

/-- A 16-bit code unit. -/
def u16 (le : Bool) (a b : Nat) : Nat := if le then a + 256 * b else 256 * a + b

/-- UTF-16 without a BOM. A surrogate that is not part of a pair is kept by
`surrogatepass`. -/
def utf16Dec (le : Bool) : Nat → List Nat → Except PyExc PStr
  | 0, _ => .error .modelFuel
  | _ + 1, [] => .ok []
  | _ + 1, [_] => .error decErr
  | f + 1, a :: b :: t =>
    let u := u16 le a b
    match t with
    | c :: d :: t' =>
      let v := u16 le c d
      if 0xd800 ≤ u ∧ u ≤ 0xdbff ∧ 0xdc00 ≤ v ∧ v ≤ 0xdfff then
        (utf16Dec le f t').map (joinSurrogates u v :: ·)
      else (utf16Dec le f t).map (u :: ·)
    | _ => (utf16Dec le f t).map (u :: ·)

/-- UTF-32 without a BOM. -/
def utf32Dec (le : Bool) : Nat → List Nat → Except PyExc PStr
  | 0, _ => .error .modelFuel
  | _ + 1, [] => .ok []
  | f + 1, a :: b :: c :: d :: t =>
    let v := if le then a + 256 * b + 65536 * c + 16777216 * d else 16777216 * a + 65536 * b + 256 * c + d
    if v ≥ 0x110000 then .error decErr else (utf32Dec le f t).map (v :: ·)
  | _ + 1, _ => .error decErr

/-- `b.decode(encoding, 'surrogatepass')` for the names `detect_encoding` returns. -/
def decodeBytes (enc : String) (b : List Nat) : Except PyExc PStr :=
  let f := b.length + 1
  if enc = "utf-8" then utf8Dec f b
  else if enc = "utf-8-sig" then utf8Dec f (b.drop 3)
  else if enc = "utf-16" then utf16Dec (b.take 2 == [0xff, 0xfe]) f (b.drop 2)
  else if enc = "utf-32" then utf32Dec (b.take 4 == [0xff, 0xfe, 0, 0]) f (b.drop 4)
  else if enc = "utf-16-le" then utf16Dec true f b
  else if enc = "utf-16-be" then utf16Dec false f b
  else if enc = "utf-32-le" then utf32Dec true f b
  else utf32Dec false f b

/-! ### `detect_encoding`, Lib/json/__init__.py:248-275 -/

def bomUtf8 : List Nat := [0xef, 0xbb, 0xbf]
def bomU16Le : List Nat := [0xff, 0xfe]
def bomU16Be : List Nat := [0xfe, 0xff]
def bomU32Le : List Nat := [0xff, 0xfe, 0, 0]
def bomU32Be : List Nat := [0, 0, 0xfe, 0xff]

def startsWith (b p : List Nat) : Bool := b.take p.length == p

def detectEncoding (b : List Nat) : String :=
  if startsWith b bomU32Be || startsWith b bomU32Le then "utf-32"
  else if startsWith b bomU16Be || startsWith b bomU16Le then "utf-16"
  else if startsWith b bomUtf8 then "utf-8-sig"
  else
    let b0 := b.getD 0 0
    let b1 := b.getD 1 0
    let b2 := b.getD 2 0
    let b3 := b.getD 3 0
    if b.length ≥ 4 then
      if b0 = 0 then (if b1 ≠ 0 then "utf-16-be" else "utf-32-be")
      else if b1 = 0 then (if b2 ≠ 0 ∨ b3 ≠ 0 then "utf-16-le" else "utf-32-le")
      else "utf-8"
    else if b.length = 2 then
      if b0 = 0 then "utf-16-be"
      else if b1 = 0 then "utf-16-le"
      else "utf-8"
    else "utf-8"

/-! ### `JSONDecoder.__init__`, decoder.py:292-337 -/

/-- A hook argument with its truth value: `parse_float or float` falls back to
`float` for a false callable. -/
abbrev HookArg := Option (Bool × (PStr → DR JVal))

/-- The keyword arguments of `json.loads`, without `cls`. -/
structure DecArgs where
  objectHook : Option (List (PStr × JVal) → DR JVal) := none
  objectPairsHook : Option (List (PStr × JVal) → DR JVal) := none
  parseFloat : HookArg := none
  parseInt : HookArg := none
  parseConstant : HookArg := none
  /-- `strict`, which `loads` passes on through `**kw`. -/
  strict : Option Bool := none
  /-- Any other keyword argument. -/
  kw : List String := []

/-- `JSONDecoder(object_hook=..., ...)`: the attributes the scanner reads. -/
def decoderInit (a : DecArgs) : Except PyExc DCfg :=
  match a.kw with
  | k :: _ => .error (.typeError s!"JSONDecoder.__init__() got an unexpected keyword argument '{k}'")
  | [] =>
    let d : DCfg := {}
    .ok { strict := a.strict.getD true
          objectHook := a.objectHook
          pairsHook := a.objectPairsHook
          parseFloat := match a.parseFloat with
            | some (true, h) => h
            | _ => d.parseFloat
          parseIntFn := match a.parseInt with
            | some (true, h) => some h
            | _ => none
          parseConstant := match a.parseConstant with
            | some (true, h) => h
            | _ => d.parseConstant }

/-! ### `json.loads`, `json.load` -/

/-- The argument of `json.loads`. -/
inductive LoadArg where
  | str (s : PStr)
  /-- `bytes` or `bytearray`. -/
  | bytes (b : List Nat)
  /-- Any other object, by type name. -/
  | other (t : String)

/-- The condition of the fast path, Lib/json/__init__.py:351-353. -/
def loadsFast (a : DecArgs) : Bool :=
  a.objectHook.isNone && a.parseInt.isNone && a.parseFloat.isNone && a.parseConstant.isNone &&
    a.objectPairsHook.isNone && a.strict.isNone && a.kw.isEmpty

/-- `_default_decoder.decode(s)` or `cls(**kw).decode(s)`, __init__.py:351-365. -/
def loadsDecode (decode : DCfg → PStr → DR JVal) (a : DecArgs) (s : PStr) : Except PyExc JVal :=
  let cfg : Except PyExc DCfg := if loadsFast a then .ok {} else decoderInit a
  match cfg with
  | .error e => .error e
  | .ok cfg =>
    match decode cfg s with
    | .ok v => .ok v
    | .error e => .error (e.toPy s)

/-- `json.loads(x, ...)`, Lib/json/__init__.py:304-365, for a given `JSONDecoder.decode`. -/
def jsonLoads (decode : DCfg → PStr → DR JVal) (a : DecArgs) : LoadArg → Except PyExc JVal
  | .str s =>
    if s.head? = some 0xfeff then
      .error ((DErr.jde "Unexpected UTF-8 BOM (decode using utf-8-sig)" 0).toPy s)
    else loadsDecode decode a s
  | .bytes b =>
    match decodeBytes (detectEncoding b) b with
    | .error e => .error e
    | .ok s => loadsDecode decode a s
  | .other t => .error (.typeError s!"the JSON object must be str, bytes or bytearray, not {t}")

/-- `json.load(fp, ...)`, __init__.py:278-301: `fp.read()` is `rd`. -/
def jsonLoad (decode : DCfg → PStr → DR JVal) (a : DecArgs) (rd : Except PyExc LoadArg) : Except PyExc JVal :=
  match rd with
  | .error e => .error e
  | .ok x => jsonLoads decode a x

/-! ### `JSONEncoder.__init__`, encoder.py:105-161 -/

/-- The `indent` argument. -/
inductive IndentArg where
  | none
  | str (s : PStr)
  | int (n : Int)

/-- The indent given to the encoders, encoder.py:249-252: `' ' * indent` for an
int, which is empty for a negative one. -/
def iterIndent : IndentArg → Option PStr
  | .none => none
  | .str s => some s
  | .int n => some (rep [32] n.toNat)

/-- The keyword arguments of `json.dumps`, without `cls`. -/
structure EncArgs where
  skipkeys : Bool := false
  ensureAscii : Bool := true
  checkCircular : Bool := true
  allowNan : Bool := true
  sortKeys : Bool := false
  indent : IndentArg := .none
  separators : Option (PStr × PStr) := none
  default : Option (Nat → String → Except PyExc EVal) := none
  /-- As `ECfg.dfltDepth`. -/
  dfltDepth : Nat := 0
  /-- Any other keyword argument. -/
  kw : List String := []

/-- `JSONEncoder(...)` followed by the option handling of `iterencode`. -/
def encoderInit (a : EncArgs) : Except PyExc ECfg :=
  match a.kw with
  | k :: _ => .error (.typeError s!"JSONEncoder.__init__() got an unexpected keyword argument '{k}'")
  | [] =>
    let d : ECfg := {}
    let (itemSep, keySep) : PStr × PStr :=
      match a.separators, a.indent with
      | some (i, k), _ => (i, k)
      | none, .none => (d.itemSep, d.keySep)
      | none, _ => (cs ",", d.keySep)
    .ok { ensureAscii := a.ensureAscii
          checkCircular := a.checkCircular
          allowNan := a.allowNan
          sortKeys := a.sortKeys
          skipKeys := a.skipkeys
          indent := iterIndent a.indent
          itemSep, keySep
          dflt := a.default.getD d.dflt
          dfltDepth := if a.default.isSome then a.dfltDepth else 0 }

/-! ### `json.dumps`, `json.dump` -/

/-- The condition of the cached encoder, Lib/json/__init__.py:230-233. -/
def dumpsFast (a : EncArgs) : Bool :=
  !a.skipkeys && a.ensureAscii && a.checkCircular && a.allowNan && a.separators.isNone &&
    a.default.isNone && !a.sortKeys && a.kw.isEmpty &&
    (match a.indent with
     | .none => true
     | _ => false)

/-- The encoder `dumps` and `dump` use. -/
def encoderOf (a : EncArgs) : Except PyExc ECfg :=
  if dumpsFast a then .ok {} else encoderInit a

/-- `json.dumps(v, ...)`, Lib/json/__init__.py:185-242, for a given `JSONEncoder.encode`. -/
def jsonDumps (encode : ECfg → EVal → ER) (a : EncArgs) (v : EVal) : ER :=
  match encoderOf a with
  | .error e => .error e
  | .ok cfg => encode cfg v

/-- `json.dump(v, fp, ...)`, __init__.py:120-182: what reaches `fp`. -/
def jsonDump (a : EncArgs) (wr : Nat → PStr → Option PyExc) (v : EVal) : Yield :=
  match encoderOf a with
  | .error e => yRaise e
  | .ok cfg => dumpTo wr (iterencode cfg v)

/-! ### The encoders of the bytes forms, for `detect_encoding`'s specification -/

def utf8Enc1 (c : Nat) : List Nat :=
  if c < 0x80 then [c]
  else if c < 0x800 then [0xc0 + c / 64, 0x80 + c % 64]
  else if c < 0x10000 then [0xe0 + c / 4096, 0x80 + c / 64 % 64, 0x80 + c % 64]
  else [0xf0 + c / 262144, 0x80 + c / 4096 % 64, 0x80 + c / 64 % 64, 0x80 + c % 64]

def utf16Enc1 (le : Bool) (c : Nat) : List Nat :=
  let unit (u : Nat) : List Nat := if le then [u % 256, u / 256] else [u / 256, u % 256]
  if c < 0x10000 then unit c
  else unit (0xd800 + (c - 0x10000) / 1024) ++ unit (0xdc00 + (c - 0x10000) % 1024)

def utf32Enc1 (le : Bool) (c : Nat) : List Nat :=
  let l := [c % 256, c / 256 % 256, c / 65536 % 256, c / 16777216]
  if le then l else l.reverse

/-- A `str` encoded in one of the encodings RFC 4627 section 3 names. -/
inductive TextEnc where
  | utf8 | utf16 (le : Bool) | utf32 (le : Bool)
  deriving DecidableEq, Repr

def TextEnc.encode : TextEnc → PStr → List Nat
  | .utf8, s => s.flatMap utf8Enc1
  | .utf16 le, s => s.flatMap (utf16Enc1 le)
  | .utf32 le, s => s.flatMap (utf32Enc1 le)

/-- The name `detect_encoding` is meant to return. -/
def TextEnc.name : TextEnc → String
  | .utf8 => "utf-8"
  | .utf16 true => "utf-16-le"
  | .utf16 false => "utf-16-be"
  | .utf32 true => "utf-32-le"
  | .utf32 false => "utf-32-be"

end PyLean.JsonMod
