import PyLean.Pickle.Enc
import PyLean.Pickle.DecPy
import PyLean.Pickle.ToolsTable

/-!
`Lib/pickletools.py`: the argument readers (`:214-928`), `_genops` and `genops`
(`:2296-2351`), `optimize` (`:2356-2418`) and `dis` (`:2423-2592`).

A reader runs over a file: the data and a position. `read_floatnl` stops at
`float()`, which needs the binary64 model, with the `Excluded` marker. `dis`
stops the same way on `repr` of a float and of a character outside Latin-1,
whose printability needs the Unicode database.
-/

namespace PyLean.Pickle

open PyLean

/-- A value returned by an argument reader. -/
inductive TV where
  | int (i : Int)
  | bool (b : Bool)
  | bytes (b : Bytes)
  | bytearray (b : Bytes)
  | str (s : List Nat)
  /-- `read_float8`: the eight bytes, big endian. -/
  | float (bits : Bytes)
  deriving Repr, DecidableEq, Inhabited

abbrev TM := StateT Nat (ReaderT Bytes (Except PyExc))

def tThrow {α : Type} (e : PyExc) : TM α := fun _ _ => .error e

def tLift {α : Type} (r : Py α) : TM α := fun s _ =>
  match r with
  | .ok a => .ok (a, s)
  | .error e => .error e

/-- `f.read(n)`. -/
def tRead (n : Nat) : TM Bytes := fun pos d =>
  let r := (d.drop pos).take n
  .ok (r, pos + r.length)

/-- `f.readline()`. -/
def tReadline : TM Bytes := fun pos d =>
  let rest := d.drop pos
  let line := match rest.findIdx? (· == nl) with
    | some i => rest.take (i + 1)
    | none => rest
  .ok (line, pos + line.length)

/-- `f.tell()`. -/
def tTell : TM Nat := fun pos _ => .ok (pos, pos)

/-! ## Argument readers -/

def readUintN (k : Nat) (name : String) : TM Nat := do
  let data ← tRead k
  if data.length = k then return leNat data
  else tThrow (.valueError s!"not enough data in stream to read {name}")

/-- `read_uint1`, `:214-224`. -/
def readUint1 : TM Nat := readUintN 1 "uint1"
/-- `read_uint2`, `:233-245`. -/
def readUint2 : TM Nat := readUintN 2 "uint2"
/-- `read_uint4`, `:275-287`. -/
def readUint4 : TM Nat := readUintN 4 "uint4"
/-- `read_uint8`, `:296-308`. -/
def readUint8 : TM Nat := readUintN 8 "uint8"

/-- `read_int4`, `:254-266`. -/
def readInt4 : TM Int := do
  let data ← tRead 4
  if data.length = 4 then return leInt data
  else tThrow (.valueError "not enough data in stream to read int4")

/-- `bytes.decode('latin-1')`. -/
def latin1 (b : Bytes) : List Nat := b.map (·.toNat)

/-- The quote handling of `read_stringnl`, `:349-358`. `data[1:-1]` of a
one-byte line is empty. -/
def stripQuotes (data : Bytes) : Py Bytes :=
  if data.head? == some 0x22 then
    if data.getLast? == some 0x22 then .ok (data.drop 1).dropLast
    else .error (.valueError "~string quote not found at both ends")
  else if data.head? == some 0x27 then
    if data.getLast? == some 0x27 then .ok (data.drop 1).dropLast
    else .error (.valueError "~string quote not found at both ends")
  else .error (.valueError "~no string quotes around")

/-- `readline` and the newline check of `read_stringnl`, `:344-347`. -/
def readRawnl : TM Bytes := do
  let data ← tReadline
  if data.getLast? == some nl then return data.dropLast
  else tThrow (.valueError "no newline found when trying to read stringnl")

/-- `read_stringnl(f)` with its defaults, `:317-362`. -/
def readStringnl : TM (List Nat) := do
  let raw ← readRawnl
  let data ← tLift (stripQuotes raw)
  let d ← tLift (escapeDecode 0 data)
  return latin1 d

/-- `read_stringnl_noescape`, `:374-375`: `stripquotes=False, encoding='utf-8'`.
The escapes are still decoded. -/
def readStringnlNoescape : TM (List Nat) := do
  let data ← readRawnl
  let d ← tLift (escapeDecode 0 data)
  match utf8Dec false d with
  | some s => return s
  | none => tThrow unicodeDecodeError

/-- `read_stringnl_noescape_pair`, `:388-395`. -/
def readStringnlNoescapePair : TM (List Nat) := do
  let a ← readStringnlNoescape
  let b ← readStringnlNoescape
  return a ++ [0x20] ++ b

/-- The length check that ends the counted readers. -/
def needBytes (n : Nat) (name : String) (data : Bytes) : TM Bytes :=
  if data.length = n then pure data
  else tThrow (.valueError s!"expected {n} bytes in a {name}, but only {data.length} remain")

/-- `read_string1`, `:411-426`. -/
def readString1 : TM (List Nat) := do
  let n ← readUint1
  let data ← tRead n
  return latin1 (← needBytes n "string1" data)

/-- `read_string4`, `:440-460`. -/
def readString4 : TM (List Nat) := do
  let n ← readInt4
  if n < 0 then tThrow (.valueError s!"string4 byte count < 0: {n}")
  else
    let data ← tRead n.toNat
    return latin1 (← needBytes n.toNat "string4" data)

/-- `read_bytes1`, `:474-489`. -/
def readBytes1 : TM Bytes := do
  let n ← readUint1
  let data ← tRead n
  needBytes n "bytes1" data

/-- The bound checks of `:517-518` and `:552-553`. -/
def readCounted (n : Nat) (name : String) : TM Bytes :=
  if n > ssizeMaxN then tThrow (.valueError s!"{name} byte count > sys.maxsize: {n}")
  else do
    let data ← tRead n
    needBytes n name data

/-- `read_bytes4`, `:502-523`. -/
def readBytes4 : TM Bytes := do readCounted (← readUint4) "bytes4"
/-- `read_bytes8`, `:536-558`. -/
def readBytes8 : TM Bytes := do readCounted (← readUint8) "bytes8"
/-- `read_bytearray8`, `:571-593`. -/
def readBytearray8 : TM Bytes := do readCounted (← readUint8) "bytearray8"

/-- `read_unicodestringnl`, `:605-617`. -/
def readUnicodestringnl : TM (List Nat) := do
  let data ← tReadline
  if data.getLast? == some nl then tLift (decodeRUE data.dropLast)
  else tThrow (.valueError "no newline found when trying to read unicodestringnl")

/-- `read_unicodestring1`, `:631-655`. -/
def readUnicodestring1 : TM (List Nat) := do
  let n ← readUint1
  let data ← tRead n
  tLift (decodeUtf8SP (← needBytes n "unicodestring1" data))

/-- `read_unicodestring4`, `:670-696`. -/
def readUnicodestring4 : TM (List Nat) := do
  let d ← readCounted (← readUint4) "unicodestring4"
  tLift (decodeUtf8SP d)

/-- `read_unicodestring8`, `:711-737`. -/
def readUnicodestring8 : TM (List Nat) := do
  let d ← readCounted (← readUint8) "unicodestring8"
  tLift (decodeUtf8SP d)

/-- `read_decimalnl_short`, `:752-772`. -/
def readDecimalnlShort : TM TV := do
  let s ← readRawnl
  if s = [0x30, 0x30] then return .bool false
  else if s = [0x30, 0x31] then return .bool true
  else return .int (← tLift (pyIntOfBytes s))

/-- `read_decimalnl_long`, `:774-788`. -/
def readDecimalnlLong : TM Int := do
  let s ← readRawnl
  let s := if s.getLast? == some 0x4c then s.dropLast else s
  tLift (pyIntOfBytes s)

/-- `read_floatnl`, `:815-822`, up to `float(s)`. -/
def readFloatnl : TM TV := do
  let _ ← readRawnl
  tThrow (excluded "float() of text")

/-- `read_float8`, `:837-850`: `_unpack(">d", data)` keeps the eight bytes. -/
def readFloat8 : TM Bytes := do
  let data ← tRead 8
  if data.length = 8 then return data
  else tThrow (.valueError "not enough data in stream to read float8")

/-- `read_long1`, `:875-894`. -/
def readLong1 : TM Int := do
  let n ← readUint1
  let data ← tRead n
  if data.length ≠ n then tThrow (.valueError "not enough data in stream to read long1")
  else return decodeLong data

/-- `read_long4`, `:907-928`. -/
def readLong4 : TM Int := do
  let n ← readInt4
  if n < 0 then tThrow (.valueError s!"long4 byte count < 0: {n}")
  else
    let data ← tRead n.toNat
    if data.length ≠ n.toNat then tThrow (.valueError "not enough data in stream to read long4")
    else return decodeLong data

def asNat (r : TM Nat) : TM TV := do return TV.int (Int.ofNat (← r))
def asInt (r : TM Int) : TM TV := do return TV.int (← r)
def asStr (r : TM (List Nat)) : TM TV := do return TV.str (← r)
def asBytes (r : TM Bytes) : TM TV := do return TV.bytes (← r)

/-- The reader of an `ArgumentDescriptor`, by name. -/
def argReader : String → Option (TM TV)
  | "uint1" => some (asNat readUint1)
  | "uint2" => some (asNat readUint2)
  | "int4" => some (asInt readInt4)
  | "uint4" => some (asNat readUint4)
  | "uint8" => some (asNat readUint8)
  | "stringnl" => some (asStr readStringnl)
  | "stringnl_noescape" => some (asStr readStringnlNoescape)
  | "stringnl_noescape_pair" => some (asStr readStringnlNoescapePair)
  | "string1" => some (asStr readString1)
  | "string4" => some (asStr readString4)
  | "bytes1" => some (asBytes readBytes1)
  | "bytes4" => some (asBytes readBytes4)
  | "bytes8" => some (asBytes readBytes8)
  | "bytearray8" => some (do return TV.bytearray (← readBytearray8))
  | "unicodestringnl" => some (asStr readUnicodestringnl)
  | "unicodestring1" => some (asStr readUnicodestring1)
  | "unicodestring4" => some (asStr readUnicodestring4)
  | "unicodestring8" => some (asStr readUnicodestring8)
  | "decimalnl_short" => some readDecimalnlShort
  | "decimalnl_long" => some (asInt readDecimalnlLong)
  | "floatnl" => some readFloatnl
  | "float8" => some (do return TV.float (← readFloat8))
  | "long1" => some (asInt readLong1)
  | "long4" => some (asInt readLong4)
  | _ => none

/-! ## `_genops` -/

/-- One item of `_genops(data, yield_end_pos=True)`. `pos` and `endPos` are
`None` for a file without `tell`. -/
structure GenOp where
  info : OpInfo
  arg : Option TV
  pos : Option Nat
  endPos : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-- `code2op.get(code.decode("latin-1"))`, `:2247-2250`. -/
def findOp (c : UInt8) : Option OpInfo := opTable.find? (·.code == c)

/-- `getpos()`, `:2300-2303`. -/
def getPos (hasTell : Bool) : TM (Option Nat) :=
  if hasTell then do return some (← tTell) else pure none

/-- `"at position %s, opcode %r unknown"`, `:2313-2315`. -/
def unknownOpMsg (pos : Option Nat) (c : UInt8) : String :=
  let p := match pos with
    | some n => toString n
    | none => "<unknown>"
  s!"at position {p}, opcode {bytesRepr [c]} unknown"

/-- `opcode.arg.reader(data)`, or `None` for an opcode without argument. -/
def readArg (info : OpInfo) : TM (Option TV) :=
  match argReader info.arg with
  | some r => do return some (← r)
  | none => pure none

/-- One round of the loop of `_genops`, `:2305-2323`. -/
def genopStep (hasTell : Bool) : TM GenOp := do
  let pos ← getPos hasTell
  let code ← tRead 1
  match code with
  | [] => tThrow (.valueError "pickle exhausted before seeing STOP")
  | c :: _ =>
    match findOp c with
    | none => tThrow (.valueError (unknownOpMsg pos c))
    | some info =>
      let arg ← readArg info
      let e ← getPos hasTell
      return ⟨info, arg, pos, e⟩

/-- The loop of `_genops`, up to `STOP`, `:2324-2326`. -/
def genopsLoop (hasTell : Bool) : Nat → TM (List GenOp)
  | 0 => tThrow .modelFuel
  | fuel + 1 => do
    let op ← genopStep hasTell
    if op.info.code == oSTOP then return [op]
    else return op :: (← genopsLoop hasTell fuel)

/-- `list(genops(data))`, `:2296-2351`. Every opcode consumes a byte, so
`len(data) + 1` rounds reach the end of the data. -/
def genops (hasTell : Bool) (data : Bytes) : Py (List GenOp) :=
  match genopsLoop hasTell (data.length + 1) 0 data with
  | .ok (r, _) => .ok r
  | .error e => .error e

/-! ## `optimize` -/

/-- `name in opcode.name`. -/
def hasSub (name sub : String) : Bool := (name.splitOn sub).length > 1

/-- The argument of a PUT or GET as a dict key: `False == 0` and `True == 1`
(`read_decimalnl_short` returns bools for `00` and `01`). -/
def memoKey : Option TV → Int
  | some (.int i) => i
  | some (.bool b) => if b then 1 else 0
  | _ => 0

/-- An item of `opcodes` in `optimize`, `:2362`. -/
inductive OptOp where
  | put (arg : Int)
  | get (arg : Int)
  | raw (pos endPos : Nat)
  deriving Repr, DecidableEq

/-- The state of the first loop of `optimize`, `:2359-2387`. -/
structure OptSt where
  oldids : List Int := []
  /-- `newids`, most recently written first. -/
  newids : List (Int × Option Nat) := []
  /-- `opcodes`, most recent first. -/
  ops : List OptOp := []
  proto : Int := 0
  header : Bytes := []

/-- `oldids.add(a)`. -/
def addId (ids : List Int) (a : Int) : List Int := if ids.contains a then ids else a :: ids

/-- `newids[arg] = None` of the first loop. Later writes of the same key change
nothing there, since no id has been assigned yet. -/
def addNew (s : List (Int × Option Nat)) (a : Int) : List (Int × Option Nat) :=
  if (s.lookup a).isSome then s else (a, none) :: s

/-- The body of the first loop of `optimize`, `:2365-2387`. -/
def optStep (p : Bytes) (s : OptSt) (op : GenOp) : OptSt :=
  let name := op.info.name
  let pos := op.pos.getD 0
  let e := op.endPos.getD 0
  if hasSub name "PUT" then
    { s with oldids := addId s.oldids (memoKey op.arg), ops := .put (memoKey op.arg) :: s.ops }
  else if name = "MEMOIZE" then
    let idx : Int := s.oldids.length
    { s with oldids := addId s.oldids idx, ops := .put idx :: s.ops }
  else if hasSub name "FRAME" then s
  else if hasSub name "GET" then
    { s with proto := max s.proto op.info.proto, newids := addNew s.newids (memoKey op.arg),
             ops := .get (memoKey op.arg) :: s.ops }
  else if name = "PROTO" then
    let s' := { s with proto := max s.proto (memoKey op.arg) }
    if pos = 0 then { s' with header := (p.drop pos).take (e - pos) }
    else { s' with ops := .raw pos e :: s'.ops }
  else { s with ops := .raw pos e :: s.ops }

/-- `pickler.get(i)` with `newids[arg]`, which is `None` for a GET of an id no
PUT wrote. -/
def optGet (proto : Nat) : Option Nat → Py Bytes
  | some i => pyGet proto i
  | none =>
    if proto ≥ 1 then
      .error (.typeError "'<' not supported between instances of 'NoneType' and 'int'")
    else .ok (oGET :: [0x4e, 0x6f, 0x6e, 0x65] ++ [nl])

/-- The state of the second loop of `optimize`, `:2399-2416`. -/
structure OptOut where
  newids : List (Int × Option Nat)
  idx : Nat := 0
  /-- Output-layer calls, most recent first. -/
  ev : List Event := []

/-- The writes that end the second loop, `:2413-2416`: `commit_frame()` and
`write` are one `boundary` and one `w`, and `commit_frame(force=True)` followed
by `file_write` is `_Framer.write_large_bytes` with an empty header. -/
def optWrite (s : OptOut) (data : Bytes) : OptOut :=
  { s with ev := .w data :: .boundary :: s.ev }

/-- The body of the second loop of `optimize`, `:2400-2416`. -/
def optEmit (proto : Nat) (p : Bytes) (s : OptOut) : OptOp → Py OptOut
  | .put arg =>
    if (s.newids.lookup arg).isNone then .ok s
    else
      match pyPut proto s.idx with
      | .ok data => .ok (optWrite { s with newids := (arg, some s.idx) :: s.newids, idx := s.idx + 1 } data)
      | .error e => .error e
  | .get arg =>
    match optGet proto (s.newids.lookup arg).join with
    | .ok data => .ok (optWrite s data)
    | .error e => .error e
  | .raw pos e =>
    let data := (p.drop pos).take (e - pos)
    if data.length > frameSizeTarget then .ok { s with ev := .large [] data :: s.ev }
    else .ok (optWrite s data)

/-- `pickletools.optimize(p)`, `:2356-2418`. -/
def optimize (p : Bytes) : Py Bytes := do
  let ops ← genops true p
  let s := ops.foldl (optStep p) {}
  let proto ← pyProtocol s.proto
  let out ← s.ops.reverse.foldlM (optEmit proto p) ({ newids := s.newids } : OptOut)
  let evs := (if proto ≥ 4 then [Event.start] else []) ++ out.ev.reverse ++ [Event.finish]
  return s.header ++ pyFrame evs

/-! ## `dis` -/

def charOf (c : Nat) : String := (Char.ofNat c).toString

def bytesText (b : Bytes) : String := String.ofList (b.map fun c => Char.ofNat c.toNat)

/-- Lowercase hex with `w` digits. -/
def hexN : Nat → Nat → String
  | 0, _ => ""
  | w + 1, n => hexN w (n / 16) ++ charOf (hexDigit (n % 16)).toNat

/-- The escapes of `unicode_repr` and of the `backslashreplace` handler. -/
def escapeCP (c : Nat) : String :=
  if c < 0x100 then "\\x" ++ hexN 2 c
  else if c < 0x10000 then "\\u" ++ hexN 4 c
  else "\\U" ++ hexN 8 c

/-- One character of `repr(s)`, or of `ascii(s)` with `asciiOnly`
(`unicode_repr`, `PyObject_ASCII`). Printability is modelled up to Latin-1:
0x80-0xa0 and 0xad are the unprintable characters there. -/
def strReprCP (asciiOnly : Bool) (q c : Nat) : Py String :=
  if c == q || c == 0x5c then .ok ("\\" ++ charOf c)
  else if c == 0x09 then .ok "\\t"
  else if c == 0x0a then .ok "\\n"
  else if c == 0x0d then .ok "\\r"
  else if c < 0x20 || c == 0x7f then .ok (escapeCP c)
  else if c < 0x7f then .ok (charOf c)
  else if asciiOnly then .ok (escapeCP c)
  else if c ≤ 0xa0 || c == 0xad then .ok (escapeCP c)
  else if c < 0x100 then .ok (charOf c)
  else .error (excluded "repr of a character outside Latin-1")

/-- `repr(s)`, or `ascii(s)` with `asciiOnly`. -/
def strRepr (asciiOnly : Bool) (s : List Nat) : Py String := do
  let q : Nat := if s.contains 0x27 && !s.contains 0x22 then 0x22 else 0x27
  let parts ← s.mapM (strReprCP asciiOnly q)
  return charOf q ++ String.join parts ++ charOf q

/-- One byte of `repr(bytearray)`. Unlike `bytes`, `'` is escaped under either
quote. -/
def bytearrayReprByte (c : UInt8) : String :=
  let n := c.toNat
  if n == 0x27 || n == 0x5c then "\\" ++ charOf n
  else if n == 0x09 then "\\t"
  else if n == 0x0a then "\\n"
  else if n == 0x0d then "\\r"
  else if n < 0x20 || n ≥ 0x7f then "\\x" ++ hexN 2 n
  else charOf n

/-- `repr(bytearray)`, `bytearray_repr_lock_held` in `Objects/bytearrayobject.c:1185-1198`:
`"` only when there is a `'` and no `"`. -/
def bytearrayRepr (b : Bytes) : String :=
  let quote := if b.contains 0x27 && !b.contains 0x22 then "\"" else "'"
  "bytearray(b" ++ quote ++ String.join (b.map bytearrayReprByte) ++ quote ++ ")"

/-- `repr(arg)`. -/
def tvRepr : TV → Py String
  | .int i => do return bytesText (← reprInt i)
  | .bool b => .ok (if b then "True" else "False")
  | .bytes b => .ok (bytesRepr b)
  | .bytearray b => .ok (bytearrayRepr b)
  | .str s => strRepr false s
  | .float _ => .error (excluded "repr of a float")

/-- `' ' * n`. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- `"%5d" % n`. -/
def fmt5 (n : Nat) : String :=
  let s := toString n
  spaces (5 - s.length) ++ s

/-- `repr(opcode.code)[1:-1]`: the codes are printable ASCII without a quote or
backslash, or `\x80` to `\x98`. -/
def codeRepr (c : UInt8) : String :=
  if c.toNat < 0x7f then charOf c.toNat else escapeCP c.toNat

/-- `"%-4s" % s`. -/
def pad4 (s : String) : String := s ++ spaces (4 - s.length)

def markObj : String := "mark"

/-- The stack and memo that `dis` emulates, `:2545-2552`. Stacks have their top
first. -/
structure DisSt where
  stack : List String := []
  memo : List (Int × String) := []
  maxproto : Int := -1
  markstack : List (Option Nat) := []
  annocol : Nat
  /-- Everything printed so far. -/
  out : String := ""

/-- An exception, with what had been printed when it was raised. -/
abbrev DM := Except (PyExc × String)

/-- The result of "See whether a MARK should be popped". -/
structure MarkRes where
  stack : List String
  markstack : List (Option Nat)
  numtopop : Nat
  markmsg : Option String
  errormsg : Option String

/-- `while stack[-1] is not markobject: stack.pop()` and the `stack.pop()` that
follows, `:2582-2584`. `stack[-1]` raises on an empty stack. -/
def popToMark : List String → Py (List String)
  | [] => .error (.indexError "list index out of range")
  | x :: r => if x == markObj then .ok r else popToMark r

def markText : Option Nat → String
  | none => "(MARK at unknown opcode offset)"
  | some p => s!"(MARK at {p})"

/-- `:2566-2592`. -/
def markPhase (info : OpInfo) (stack : List String) (markstack : List (Option Nat)) : Py MarkRes :=
  let n := info.before.length
  if info.before.contains markObj || (info.name == "POP" && stack.head? == some markObj) then
    match markstack with
    | [] => .ok ⟨stack, [], n, none, some "no MARK exists on stack"⟩
    | mp :: rest =>
      match popToMark stack with
      | .ok st =>
        let top := if info.before.contains markObj then info.before.idxOf markObj else 0
        .ok ⟨st, rest, top, some (markText mp), none⟩
      | .error e => .error e
  else .ok ⟨stack, markstack, n, none, none⟩

/-- `memo[k] = v`. -/
def memoStore (memo : List (Int × String)) (k : Int) (v : String) : List (Int × String) :=
  (k, v) :: memo.filter (·.1 != k)

/-- The result of "Check for correct memo usage". -/
structure MemoRes where
  memo : List (Int × String)
  after : List String
  markmsg : Option String
  errormsg : Option String

/-- `:2594-2617`. -/
def memoPhase (info : OpInfo) (arg : Option TV) (stack : List String) (memo : List (Int × String))
    (markmsg errormsg : Option String) : Py MemoRes :=
  let name := info.name
  if name == "PUT" || name == "BINPUT" || name == "LONG_BINPUT" || name == "MEMOIZE" then
    let k : Int := if name == "MEMOIZE" then memo.length else memoKey arg
    let msg := if name == "MEMOIZE" then some s!"(as {k})" else markmsg
    match stack with
    | [] => .ok ⟨memo, info.after, msg, some "stack is empty -- can't store into memo"⟩
    | x :: _ =>
      if x == markObj then .ok ⟨memo, info.after, msg, some "can't store markobject in the memo"⟩
      else .ok ⟨memoStore memo k x, info.after, msg, errormsg⟩
  else if name == "GET" || name == "BINGET" || name == "LONG_BINGET" then
    match memo.lookup (memoKey arg) with
    | some v => .ok ⟨memo, [v], markmsg, errormsg⟩
    | none =>
      match arg with
      | some a =>
        match tvRepr a with
        | .ok r => .ok ⟨memo, info.after, markmsg, some s!"memo key {r} has never been stored into"⟩
        | .error e => .error e
      | none => .ok ⟨memo, info.after, markmsg, errormsg⟩
  else .ok ⟨memo, info.after, markmsg, errormsg⟩

/-- `:2619-2628`. -/
def argText (info : OpInfo) (arg : Option TV) (markmsg : Option String) (line : String) : Py String :=
  if arg.isNone && markmsg.isNone then .ok line
  else do
    let l := line ++ spaces (10 - info.name.length)
    let l ← match arg with
      | none => pure l
      | some a =>
        let r ← match info.name, a with
          | "STRING", .str s | "BINSTRING", .str s | "SHORT_BINSTRING", .str s => strRepr true s
          | _, _ => tvRepr a
        pure (l ++ " " ++ r)
    match markmsg with
    | some m => return l ++ " " ++ m
    | none => return l

/-- `:2629-2635`: the line and the new `annocol`. -/
def annotateLine (info : OpInfo) (annotate annocol : Nat) (line : String) : String × Nat :=
  if annotate = 0 then (line, annocol)
  else
    let l := line ++ spaces (annocol - line.length)
    let col := if l.length > 50 then annotate else l.length
    (l ++ " " ++ info.doc, col)

/-- Lift a `Py` step: an exception keeps the text printed so far. -/
def dmLift {α : Type} (out : String) : Py α → DM α
  | .ok a => .ok a
  | .error e => .error (e, out)

/-- The stack effects, `:2643-2653`. -/
def stackPhase (out : String) (stack : List String) (markstack : List (Option Nat)) (numtopop : Nat)
    (after : List String) (pos : Option Nat) : DM (List String × List (Option Nat)) :=
  if stack.length < numtopop then
    .error (.valueError s!"tries to pop {numtopop} items from stack with only {stack.length} items", out)
  else
    let ms := if after.contains markObj then pos :: markstack else markstack
    .ok (after.reverse ++ stack.drop numtopop, ms)

/-- The body of the loop of `dis`, `:2554-2653`. -/
def disStep (indentlevel annotate : Nat) (s : DisSt) (op : GenOp) : DM DisSt := do
  let info := op.info
  let out := match op.pos with
    | some p => s.out ++ fmt5 p ++ ": "
    | none => s.out
  let line := pad4 (codeRepr info.code) ++ " " ++ spaces (indentlevel * s.markstack.length) ++ info.name
  let m ← dmLift out (markPhase info s.stack s.markstack)
  let k ← dmLift out (memoPhase info op.arg m.stack s.memo m.markmsg m.errormsg)
  let line ← dmLift out (argText info op.arg k.markmsg line)
  let (line, col) := annotateLine info annotate s.annocol line
  let out := out ++ line ++ "\n"
  match k.errormsg with
  | some msg => .error (.valueError msg, out)
  | none =>
    let (stack, ms) ← stackPhase out m.stack m.markstack m.numtopop k.after op.pos
    return { stack, memo := k.memo, maxproto := max s.maxproto info.proto, markstack := ms,
             annocol := col, out }

/-- `:2655-2657`. -/
def disEnd (s : DisSt) : String × Option PyExc :=
  let out := s.out ++ s!"highest protocol among opcodes = {s.maxproto}\n"
  if s.stack.isEmpty then (out, none)
  else
    let names := ", ".intercalate s.stack.reverse
    (out, some (.valueError s!"stack not empty after STOP: [{names}]"))

/-- `genops` feeds the loop lazily, so what was printed before a malformed
opcode stays printed. -/
def disLoop (hasTell : Bool) (indentlevel annotate : Nat) (data : Bytes) :
    Nat → Nat → DisSt → String × Option PyExc
  | 0, _, s => (s.out, some .modelFuel)
  | fuel + 1, pos, s =>
    match genopStep hasTell pos data with
    | .error e => (s.out, some e)
    | .ok (op, pos') =>
      match disStep indentlevel annotate s op with
      | .error (e, out) => (out, some e)
      | .ok s' =>
        if op.info.code == oSTOP then disEnd s'
        else disLoop hasTell indentlevel annotate data fuel pos' s'

/-- `dis(data, out, memo, indentlevel, annotate)`, `:2502-2657`: the text it
printed, and the exception it raised. -/
def dis (hasTell : Bool) (data : Bytes) (memo : List (Int × String)) (indentlevel annotate : Nat) :
    String × Option PyExc :=
  disLoop hasTell indentlevel annotate data (data.length + 1) 0 { memo, annocol := annotate }

end PyLean.Pickle
